//! A pass that propagates the known ranges of SSA locals.
//! We can know the ranges of SSA locals in certain locations for the following code:
//! ```
//! fn foo(a: u32) {
//!   let b = a < 9; // the integer representation of b is within the full range [0, 2).
//!   if b {
//!     let c = b; // c is true since b is within the range [1, 2).
//!     let d = a < 8; // d is true since a is within the range [0, 9).
//!   }
//! }
//! ```
//!
//! ```
//! fn boo(u: u8) -> bool {
//!   let larger = u as usize; // in terms of integer casts, u's range is known.
//!                            // in this case its [0, 255]
//!   larger < 256usize        // it is always true...
//! }
//! ```
use std::cmp::Ordering;

use rustc_abi::{Size, WrappingRange};
use rustc_const_eval::interpret::Scalar;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::visit::MutVisitor;
use rustc_middle::mir::{BasicBlock, Body, Location, Operand, Place, TerminatorKind, *};
use rustc_middle::ty::{self as rty, Ty, TyCtxt, TypingEnv};
use rustc_span::DUMMY_SP;

use crate::PassPolicy;
use crate::ssa::SsaLocals;

pub(super) struct SsaRangePropagation;

impl<'tcx> crate::MirPass<'tcx> for SsaRangePropagation {
    fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {
        PassPolicy::optional(ctx.mir_opt_level() >= 2)
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let typing_env = body.typing_env(tcx);
        let ssa = SsaLocals::new(tcx, body, typing_env);
        // Clone dominators because we need them while mutating the body.
        let dominators = body.basic_blocks.dominators().clone();
        let mut range_set =
            RangeSet::new(tcx, typing_env, body, &ssa, &body.local_decls, dominators);

        let reverse_postorder = body.basic_blocks.reverse_postorder().to_vec();
        for bb in reverse_postorder {
            let data = &mut body.basic_blocks.as_mut_preserves_cfg()[bb];
            range_set.visit_basic_block_data(bb, data);
        }
    }
}

struct RangeSet<'tcx, 'body, 'a> {
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ssa: &'a SsaLocals,
    local_decls: &'body LocalDecls<'tcx>,
    dominators: Dominators<BasicBlock>,
    /// Known ranges at each locations.
    ranges: FxHashMap<Place<'tcx>, Vec<(Location, WrappingRange)>>,
    /// Determines if the basic block has a single unique predecessor.
    unique_predecessors: DenseBitSet<BasicBlock>,
}

impl<'tcx, 'body, 'a> RangeSet<'tcx, 'body, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        typing_env: TypingEnv<'tcx>,
        body: &Body<'tcx>,
        ssa: &'a SsaLocals,
        local_decls: &'body LocalDecls<'tcx>,
        dominators: Dominators<BasicBlock>,
    ) -> Self {
        let predecessors = body.basic_blocks.predecessors();
        let mut unique_predecessors = DenseBitSet::new_empty(body.basic_blocks.len());
        for bb in body.basic_blocks.indices() {
            if predecessors[bb].len() == 1 {
                unique_predecessors.insert(bb);
            }
        }
        RangeSet {
            tcx,
            typing_env,
            ssa,
            local_decls,
            dominators,
            ranges: FxHashMap::default(),
            unique_predecessors,
        }
    }

    /// Create a new known range at the location.
    fn insert_range(&mut self, place: Place<'tcx>, location: Location, range: WrappingRange) {
        assert!(self.is_ssa(place));
        self.ranges.entry(place).or_default().push((location, range));
    }

    /// Get the known range at the location.
    fn get_range(&self, place: &Place<'tcx>, location: Location) -> Option<WrappingRange> {
        let Some(ranges) = self.ranges.get(place) else {
            return None;
        };

        let ty = place.ty(self.local_decls, self.tcx).ty;
        let layout = self.tcx.layout_of(self.typing_env.as_query_input(ty)).ok()?;
        // FIXME: we are doing intersections right now, but we have to dealt with the case when
        // theres *no* intersection, currently, None means theres no recorded range for this value,
        // instead of there is no valid range for the given place.
        let range = ranges
            .iter()
            .filter(|(range_loc, _)| range_loc.dominates(location, &self.dominators))
            .map(|(_, range)| *range)
            .reduce(|acc, v| {
                if let Some(v) = intersect(acc, v, layout.size) {
                    v
                } else {
                    // TODO: There is no intersections...
                    // but we do not handle this case
                    // the current behaivor is pretend it exisit with the previous
                    // range
                    acc
                }
            })?;
        Some(range)
    }

    fn try_as_constant(
        &mut self,
        place: Place<'tcx>,
        location: Location,
    ) -> Option<ConstOperand<'tcx>> {
        if let Some(range) = self.get_range(&place, location)
            && range.start == range.end
        {
            let ty = place.ty(self.local_decls, self.tcx).ty;
            let layout = self.tcx.layout_of(self.typing_env.as_query_input(ty)).ok()?;
            let value = ConstValue::Scalar(Scalar::from_uint(range.start, layout.size));
            let const_ = Const::Val(value, ty);
            return Some(ConstOperand { span: DUMMY_SP, user_ty: None, const_ });
        }
        None
    }

    fn is_ssa(&self, place: Place<'tcx>) -> bool {
        self.ssa.is_ssa(place.local) && place.is_stable_offset()
    }

    fn resolve_comparison(
        &mut self,
        op: ComparisonOp,
        p: Place<'tcx>,
        l: Location,
        r: Box<ConstOperand<'tcx>>,
        ty: Ty<'tcx>,
    ) -> Option<bool> {
        let range = self.get_range(&p, l)?;
        let t_width = match ty.kind() {
            rty::Int(i) => {
                i.bit_width().unwrap_or_else(|| self.tcx.data_layout.pointer_size().bits())
            }
            rty::Uint(u) => {
                u.bit_width().unwrap_or_else(|| self.tcx.data_layout.pointer_size().bits())
            }
            rty::Char => size_of::<char>() as u64 * 8,
            rty::Bool => 1,
            _ => unreachable!("Integter to Integer cast should only have integers, obviously"),
        };

        let target_value = r.const_.try_to_bits(Size::from_bits(t_width))?;
        let is_signed = matches!(ty.kind(), rty::Int(_));

        match op {
            ComparisonOp::Eq => {
                if range.contains(target_value) {
                    None
                } else {
                    Some(false)
                }
            }
            ComparisonOp::Ne => {
                if range.contains(target_value) {
                    None
                } else {
                    Some(true)
                }
            }
            op if is_signed => {
                let size = Size::from_bits(t_width);
                let start = size.sign_extend(range.start);
                let end = size.sign_extend(range.end);
                let target = size.sign_extend(target_value);
                if range.no_signed_wraparound(size) == Ok(true) {
                    match op {
                        ComparisonOp::Gt => {
                            if end <= target {
                                Some(false)
                            } else if start > target {
                                Some(true)
                            } else {
                                None
                            }
                        }
                        ComparisonOp::Ge => {
                            if end < target {
                                Some(false)
                            } else if start >= target {
                                Some(true)
                            } else {
                                None
                            }
                        }
                        ComparisonOp::Lt => {
                            if start >= target {
                                Some(false)
                            } else if end < target {
                                Some(true)
                            } else {
                                None
                            }
                        }
                        ComparisonOp::Le => {
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
                } else {
                    None
                }
            }
            op => {
                if range.no_unsigned_wraparound(Size::from_bits(t_width)) == Ok(true) {
                    match op {
                        ComparisonOp::Gt => {
                            if range.end <= target_value {
                                Some(false)
                            } else if range.start > target_value {
                                Some(true)
                            } else {
                                None
                            }
                        }
                        ComparisonOp::Ge => {
                            if range.end < target_value {
                                Some(false)
                            } else if range.start >= target_value {
                                Some(true)
                            } else {
                                None
                            }
                        }
                        ComparisonOp::Lt => {
                            if range.start >= target_value {
                                Some(false)
                            } else if range.end < target_value {
                                Some(true)
                            } else {
                                None
                            }
                        }
                        ComparisonOp::Le => {
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
    }
}

impl<'tcx> MutVisitor<'tcx> for RangeSet<'tcx, '_, '_> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_operand(&mut self, operand: &mut Operand<'tcx>, location: Location) {
        // Attempts to simplify an operand to a constant value.
        if let Some(place) = operand.place()
            && let Some(const_) = self.try_as_constant(place, location)
        {
            *operand = Operand::Constant(Box::new(const_));
        };
    }

    fn visit_statement(&mut self, statement: &mut Statement<'tcx>, location: Location) {
        self.super_statement(statement, location);
        match &mut statement.kind {
            StatementKind::Assign((place, r)) => {
                let successor = location.successor_within_block();
                let overwrite = match r {
                    Rvalue::Cast(CastKind::IntToInt, op, ty) => {
                        if self.is_ssa(*place) {
                            let t_width = match ty.kind() {
                                rty::Int(i) => i
                                    .bit_width()
                                    .unwrap_or_else(|| self.tcx.data_layout.pointer_size().bits()),
                                rty::Uint(u) => u
                                    .bit_width()
                                    .unwrap_or_else(|| self.tcx.data_layout.pointer_size().bits()),
                                rty::Char => size_of::<char>() as u64 * 8,
                                rty::Bool => 1,
                                _ => unreachable!(
                                    "Integter to Integer cast should only have integers, obviously"
                                ),
                            };
                            self.insert_range(
                                *place,
                                successor,
                                range(self.tcx, op.ty(self.local_decls, self.tcx), t_width),
                            );
                        }
                        None
                    }
                    Rvalue::BinaryOp(op, (l, r)) => {
                        let lty = l.ty(self.local_decls, self.tcx).clone();
                        let rty = r.ty(self.local_decls, self.tcx).clone();
                        match (l, r) {
                            (Operand::Constant(c), Operand::Move(p) | Operand::Copy(p)) => {
                                ComparisonOp::from(*op)
                                    .map(|v| {
                                        self.resolve_comparison(
                                            v.flip(),
                                            *p,
                                            location,
                                            c.clone(),
                                            lty,
                                        )
                                    })
                                    .flatten()
                            }
                            (Operand::Move(p) | Operand::Copy(p), Operand::Constant(c)) => {
                                ComparisonOp::from(*op)
                                    .map(|v| {
                                        self.resolve_comparison(v, *p, location, c.clone(), rty)
                                    })
                                    .flatten()
                            }
                            _ => None,
                        }
                        .map(|v| {
                            if self.is_ssa(*place) {
                                if v {
                                    self.insert_range(
                                        *place,
                                        successor,
                                        WrappingRange { start: 1, end: 1 },
                                    );
                                } else {
                                    self.insert_range(
                                        *place,
                                        successor,
                                        WrappingRange { start: 0, end: 0 },
                                    );
                                }
                            }
                            Rvalue::Use(
                                Operand::Constant(Box::new(ConstOperand {
                                    span: statement.source_info.span,
                                    user_ty: None,
                                    const_: Const::from_bool(self.tcx, v),
                                })),
                                WithRetag::No,
                            )
                        })
                    }
                    _ => None,
                };
                if let Some(overwrite) = overwrite {
                    *r = overwrite;
                }
            }
            StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(operand))
                if let Some(place) = operand.place()
                    && self.is_ssa(place) =>
            {
                let successor = location.successor_within_block();
                let range = WrappingRange { start: 1, end: 1 };
                self.insert_range(place, successor, range);
            }
            _ => {}
        }
    }

    fn visit_terminator(&mut self, terminator: &mut Terminator<'tcx>, location: Location) {
        self.super_terminator(terminator, location);
        match &terminator.kind {
            TerminatorKind::Assert { cond, expected, target, msg, .. }
                if let Some(place) = cond.place()
                    && self.is_ssa(place) =>
            {
                let successor = target.start_location();
                if location.strictly_dominates(successor, &self.dominators)
                    // Don't propagate range information from built-in overflow checks,
                    // this MIR might be lowered without them!
                    && !msg.is_optional_overflow_check()
                {
                    let val = *expected as u128;
                    let range = WrappingRange { start: val, end: val };
                    self.insert_range(place, successor, range);
                }
            }
            TerminatorKind::SwitchInt { discr, targets }
                if let Some(place) = discr.place()
                    && self.is_ssa(place)
                    // Reduce the potential compile-time overhead.
                    && targets.all_targets().len() < 16 =>
            {
                let mut distinct_targets: FxHashMap<BasicBlock, u64> = FxHashMap::default();
                for (_, target) in targets.iter() {
                    let targets = distinct_targets.entry(target).or_default();
                    *targets += 1;
                }
                for (val, target) in targets.iter() {
                    if distinct_targets[&target] != 1 {
                        // FIXME: For multiple targets, the range can be the union of their values.
                        continue;
                    }
                    let successor = target.start_location();
                    if self.unique_predecessors.contains(successor.block) {
                        assert_ne!(location.block, successor.block);
                        let range = WrappingRange { start: val, end: val };
                        self.insert_range(place, successor, range);
                    }
                }

                // FIXME: The range for the otherwise target be extend to more types.
                // For instance, `val` is within the range [4, 1) at the otherwise target of `matches!(val, 1 | 2 | 3)`.
                let otherwise = targets.otherwise().start_location();
                if place.ty(self.local_decls, self.tcx).ty.is_bool()
                    && let [val] = targets.all_values()
                    && self.unique_predecessors.contains(otherwise.block)
                {
                    assert_ne!(location.block, otherwise.block);
                    let range = if val.get() == 0 {
                        WrappingRange { start: 1, end: 1 }
                    } else {
                        WrappingRange { start: 0, end: 0 }
                    };
                    self.insert_range(place, otherwise, range);
                }
            }
            _ => {}
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ComparisonOp {
    Gt,
    Ge,
    Lt,
    Le,
    Eq,
    Ne,
}

impl ComparisonOp {
    fn flip(self) -> Self {
        match self {
            ComparisonOp::Gt => ComparisonOp::Lt,
            ComparisonOp::Ge => ComparisonOp::Le,
            ComparisonOp::Lt => ComparisonOp::Gt,
            ComparisonOp::Le => ComparisonOp::Ge,
            v => v,
        }
    }

    fn from(op: BinOp) -> Option<Self> {
        match op {
            BinOp::Gt => Some(ComparisonOp::Gt),
            BinOp::Ge => Some(ComparisonOp::Ge),
            BinOp::Lt => Some(ComparisonOp::Lt),
            BinOp::Le => Some(ComparisonOp::Le),
            BinOp::Eq => Some(ComparisonOp::Eq),
            BinOp::Ne => Some(ComparisonOp::Ne),
            _ => None,
        }
    }
}

#[inline]
fn intersect(l: WrappingRange, r: WrappingRange, size: Size) -> Option<WrappingRange> {
    let max = mask(size.bits());

    let intersection = |a: u128, b: u128, c: u128, d: u128| {
        let start = a.max(c);
        let end = b.min(d);
        (start <= end).then_some(WrappingRange { start, end })
    };

    match (l.start > l.end, r.start > r.end) {
        (false, false) => intersection(l.start, l.end, r.start, r.end),

        (true, true) => {
            // we cound be conservative here, if it is really hurting the performance,
            // we can just keep the first branch
            if r.end >= l.start || l.end >= r.start {
                let l_gap = l.start - l.end - 1;
                let r_gap = r.start - r.end - 1;

                Some(if l_gap >= r_gap { l } else { r })
            } else {
                let lo = l.end.min(r.end);
                let hi = l.start.max(r.start);

                Some(WrappingRange { start: hi, end: lo })
            }
        }

        (true, false) | (false, true) => {
            let (w, n) = if l.start > l.end { (l, r) } else { (r, l) };

            let low = intersection(0, w.end, n.start, n.end);
            let high = intersection(w.start, max, n.start, n.end);

            match (low, high) {
                (None, None) => None,
                (Some(a), None) | (None, Some(a)) => Some(a),
                (Some(a), Some(b)) => {
                    let inner_gap = b.start - a.end - 1;
                    let outer_gap = (max - b.end) + a.start;

                    if inner_gap >= outer_gap {
                        Some(WrappingRange { start: b.start, end: a.end })
                    } else {
                        Some(WrappingRange { start: a.start, end: b.end })
                    }
                }
            }
        }
    }
}
