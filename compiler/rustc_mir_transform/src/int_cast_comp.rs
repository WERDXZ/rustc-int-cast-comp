use std::cmp::{Ord, Ordering};

use rustc_abi::{Size, WrappingRange};
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::*;
use rustc_middle::ty::{self as rty, Ty, TyCtxt};
use tracing::trace;

use crate::PassPolicy;
use crate::ssa::SsaLocals;

pub(super) struct IntCastComparison;

impl<'tcx> crate::MirPass<'tcx> for IntCastComparison {
    fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {
        PassPolicy::optional(ctx.mir_opt_level() >= 2)
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        trace!("Running SimplifyIntCastComparison on {:?}", body.source);
        let typing_env = body.typing_env(tcx);
        let ssa = SsaLocals::new(tcx, body, typing_env);
        // maybe IndexMap
        let interest: FxHashMap<_, _> = ssa
            .assignments(body)
            .filter_map(|(lvalue, rvalue, _)| match rvalue {
                Rvalue::Cast(CastKind::IntToInt, op, ty) => {
                    let t_width = match ty.kind() {
                        rty::Int(i) => {
                            i.bit_width().unwrap_or_else(|| tcx.data_layout.pointer_size().bits())
                        }
                        rty::Uint(u) => {
                            u.bit_width().unwrap_or_else(|| tcx.data_layout.pointer_size().bits())
                        }
                        rty::Char => size_of::<char>() as u64 * 8,
                        rty::Bool => 1,
                        _ => unreachable!(
                            "Integter to Integer cast should only have integers, obviously"
                        ),
                    };
                    Some((
                        lvalue,
                        (range(tcx, op.ty(&body.local_decls, tcx), t_width), t_width, *ty),
                    ))
                }
                _ => None,
            })
            .collect();

        let resolve = |op: SupportedOp, l: Place<'tcx>, r: Box<ConstOperand<'tcx>>| {
            let (range, t_width, ty) = interest.get(&l.local)?;
            let target_value = r.const_.try_to_bits(Size::from_bits(*t_width))?;
            let is_signed = matches!(ty.kind(), rty::Int(_));

            match op {
                SupportedOp::Eq => {
                    if range.contains(target_value) {
                        None
                    } else {
                        Some(false)
                    }
                }
                SupportedOp::Ne => {
                    if range.contains(target_value) {
                        None
                    } else {
                        Some(true)
                    }
                }
                op if is_signed => {
                    let size = Size::from_bits(*t_width);
                    let start = size.sign_extend(range.start);
                    let end = size.sign_extend(range.end);
                    let target = size.sign_extend(target_value);
                    if range.is_full_for(size) {
                        None
                    } else {
                        match op {
                            SupportedOp::Gt => {
                                if end <= target {
                                    Some(false)
                                } else if start > target {
                                    Some(true)
                                } else {
                                    None
                                }
                            }
                            SupportedOp::Ge => {
                                if end < target {
                                    Some(false)
                                } else if start >= target {
                                    Some(true)
                                } else {
                                    None
                                }
                            }
                            SupportedOp::Lt => {
                                if start >= target {
                                    Some(false)
                                } else if end < target {
                                    Some(true)
                                } else {
                                    None
                                }
                            }
                            SupportedOp::Le => {
                                if start > target {
                                    Some(false)
                                } else if end <= target {
                                    Some(true)
                                } else {
                                    None
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                }
                op => {
                    if range.no_unsigned_wraparound(Size::from_bits(*t_width)) == Ok(true) {
                        match op {
                            SupportedOp::Gt => {
                                if range.end <= target_value {
                                    Some(false)
                                } else if range.start > target_value {
                                    Some(true)
                                } else {
                                    None
                                }
                            }
                            SupportedOp::Ge => {
                                if range.end < target_value {
                                    Some(false)
                                } else if range.start >= target_value {
                                    Some(true)
                                } else {
                                    None
                                }
                            }
                            SupportedOp::Lt => {
                                if range.start >= target_value {
                                    Some(false)
                                } else if range.end < target_value {
                                    Some(true)
                                } else {
                                    None
                                }
                            }
                            SupportedOp::Le => {
                                if range.start > target_value {
                                    Some(false)
                                } else if range.end <= target_value {
                                    Some(true)
                                } else {
                                    None
                                }
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        None
                    }
                }
            }
        };

        for data in body.basic_blocks.as_mut_preserves_cfg() {
            data.statements.iter_mut().for_each(|st| {
                match &mut st.kind {
                    StatementKind::Assign((_, rvalue)) => {
                        let res = match rvalue {
                            Rvalue::BinaryOp(op, (l, r)) => match (l, r) {
                                (Operand::Constant(c), Operand::Move(p) | Operand::Copy(p)) => {
                                    SupportedOp::from(*op)
                                        .map(|v| resolve(v.flip(), *p, c.clone()))
                                        .flatten()
                                }
                                (Operand::Move(p) | Operand::Copy(p), Operand::Constant(c)) => {
                                    SupportedOp::from(*op)
                                        .map(|v| resolve(v, *p, c.clone()))
                                        .flatten()
                                }
                                _ => None,
                            },
                            _ => None,
                        };
                        if let Some(v) = res {
                            *rvalue = Rvalue::Use(
                                Operand::Constant(Box::new(ConstOperand {
                                    span: st.source_info.span,
                                    user_ty: None,
                                    const_: Const::from_bool(tcx, v),
                                })),
                                WithRetag::No,
                            )
                        }
                    }
                    _ => {}
                };
            });
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SupportedOp {
    Gt,
    Ge,
    Lt,
    Le,
    Eq,
    Ne,
}

impl SupportedOp {
    fn flip(self) -> Self {
        match self {
            SupportedOp::Gt => SupportedOp::Lt,
            SupportedOp::Ge => SupportedOp::Le,
            SupportedOp::Lt => SupportedOp::Gt,
            SupportedOp::Le => SupportedOp::Ge,
            v => v,
        }
    }

    fn from(op: BinOp) -> Option<Self> {
        match op {
            BinOp::Gt => Some(SupportedOp::Gt),
            BinOp::Ge => Some(SupportedOp::Ge),
            BinOp::Lt => Some(SupportedOp::Lt),
            BinOp::Le => Some(SupportedOp::Le),
            BinOp::Eq => Some(SupportedOp::Eq),
            BinOp::Ne => Some(SupportedOp::Ne),
            _ => None,
        }
    }
}

// return the bitrange of the type
// negative means an negative value bound
// Range non-inclusive: [.0, .1)
fn range(tcx: TyCtxt<'_>, from: Ty<'_>, t_width: u64) -> WrappingRange {
    match from.kind() {
        rty::Int(f) => {
            let f_width = f.bit_width().unwrap_or_else(|| tcx.data_layout.pointer_size().bits());
            match Ord::cmp(&f_width, &t_width) {
                Ordering::Less => WrappingRange {
                    start: (u128::MAX << (f_width - 1)) & mask(t_width),
                    end: mask(f_width - 1),
                },
                Ordering::Equal | Ordering::Greater => {
                    WrappingRange::full(Size::from_bits(t_width))
                }
            }
        }
        rty::Uint(f) => {
            let f_width = f.bit_width().unwrap_or_else(|| tcx.data_layout.pointer_size().bits());
            WrappingRange::full(Size::from_bits(f_width.min(t_width)))
        }
        rty::Char => {
            let f_width = size_of::<char>() as u64 * 8;
            WrappingRange::full(Size::from_bits(f_width.min(t_width)))
        }
        rty::Bool => WrappingRange { start: 0, end: 1 },
        _ => unreachable!("Integter to Integer cast should only have integers, obviously"),
    }
}

#[inline(always)]
fn mask(bits: u64) -> u128 {
    u128::MAX >> (128 - bits)
}
