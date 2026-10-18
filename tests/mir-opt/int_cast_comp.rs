//@ test-mir-pass: IntCastComparison
//@ compile-flags: -Zmir-enable-passes=+GVN
//@ skip-filecheck

// EMIT_MIR int_cast_comp.u8_to_i32_negative.IntCastComparison.diff
// EMIT_MIR int_cast_comp.i8_to_i32_above.IntCastComparison.diff
// EMIT_MIR int_cast_comp.i8_to_i32_below.IntCastComparison.diff
// EMIT_MIR int_cast_comp.i8_to_i32_edges.IntCastComparison.diff
// EMIT_MIR int_cast_comp.i8_to_u32_gap.IntCastComparison.diff
// EMIT_MIR int_cast_comp.u16_to_u8.IntCastComparison.diff
// EMIT_MIR int_cast_comp.u16_to_i8.IntCastComparison.diff
// EMIT_MIR int_cast_comp.i16_to_u8.IntCastComparison.diff
// EMIT_MIR int_cast_comp.i16_to_i8.IntCastComparison.diff
// EMIT_MIR int_cast_comp.u8_to_i8.IntCastComparison.diff
// EMIT_MIR int_cast_comp.i8_to_u8.IntCastComparison.diff
// EMIT_MIR int_cast_comp.bool_to_u32.IntCastComparison.diff
// EMIT_MIR int_cast_comp.char_to_u64.IntCastComparison.diff
// EMIT_MIR int_cast_comp.u64_to_i128.IntCastComparison.diff
// EMIT_MIR int_cast_comp.i64_to_u128_gap.IntCastComparison.diff
// EMIT_MIR int_cast_comp.constant_left.IntCastComparison.diff

struct TestResult {
    gt: bool,
    ge: bool,
    lt: bool,
    le: bool,
    eq: bool,
    ne: bool,
}

fn u8_to_i32_negative(l: u8) -> TestResult {
    let l = l as i32;
    TestResult {
        gt: l > -1,
        ge: l >= -1,
        lt: l < -1,
        le: l <= -1,
        eq: l == -1,
        ne: l != -1,
    }
}

fn i8_to_i32_above(l: i8) -> TestResult {
    let l = l as i32;
    TestResult {
        gt: l > 420,
        ge: l >= 421,
        lt: l < 422,
        le: l <= 423,
        eq: l == 424,
        ne: l != 425,
    }
}

fn i8_to_i32_below(l: i8) -> TestResult {
    let l = l as i32;
    TestResult {
        gt: l > -129,
        ge: l >= -130,
        lt: l < -131,
        le: l <= -132,
        eq: l == -133,
        ne: l != -134,
    }
}

fn i8_to_i32_edges(l: i8) -> TestResult {
    let l = l as i32;
    TestResult {
        gt: l > 127,
        ge: l >= -128,
        lt: l < -128,
        le: l <= 127,
        eq: l == -129,
        ne: l != 128,
    }
}

fn i8_to_u32_gap(l: i8) -> TestResult {
    let l = l as u32;
    TestResult {
        gt: l > 256,
        ge: l >= 257,
        lt: l < 258,
        le: l <= 259,
        eq: l == 260,
        ne: l != 261,
    }
}

fn u16_to_u8(l: u16) -> TestResult {
    let l = l as u8;
    TestResult {
        gt: l > 42,
        ge: l >= 43,
        lt: l < 44,
        le: l <= 45,
        eq: l == 46,
        ne: l != 47,
    }
}

fn u16_to_i8(l: u16) -> TestResult {
    let l = l as i8;
    TestResult {
        gt: l > -1,
        ge: l >= -2,
        lt: l < -3,
        le: l <= -4,
        eq: l == -5,
        ne: l != -6,
    }
}

fn i16_to_u8(l: i16) -> TestResult {
    let l = l as u8;
    TestResult {
        gt: l > 42,
        ge: l >= 43,
        lt: l < 44,
        le: l <= 45,
        eq: l == 46,
        ne: l != 47,
    }
}

fn i16_to_i8(l: i16) -> TestResult {
    let l = l as i8;
    TestResult {
        gt: l > -1,
        ge: l >= -2,
        lt: l < -3,
        le: l <= -4,
        eq: l == -5,
        ne: l != -6,
    }
}

fn u8_to_i8(l: u8) -> TestResult {
    let l = l as i8;
    TestResult {
        gt: l > -1,
        ge: l >= -2,
        lt: l < -3,
        le: l <= -4,
        eq: l == -5,
        ne: l != -6,
    }
}

fn i8_to_u8(l: i8) -> TestResult {
    let l = l as u8;
    TestResult {
        gt: l > 42,
        ge: l >= 43,
        lt: l < 44,
        le: l <= 45,
        eq: l == 46,
        ne: l != 47,
    }
}

fn bool_to_u32(l: bool) -> TestResult {
    let l = l as u32;
    TestResult {
        gt: l > 1,
        ge: l >= 0,
        lt: l < 2,
        le: l <= 1,
        eq: l == 2,
        ne: l != 2,
    }
}

fn char_to_u64(l: char) -> TestResult {
    let l = l as u64;
    TestResult {
        gt: l > 0x10ffff,
        ge: l >= 0x110000,
        lt: l < 0x110000,
        le: l <= 0x10ffff,
        eq: l == 0xd800,
        ne: l != 0xd800,
    }
}

fn u64_to_i128(l: u64) -> TestResult {
    let l = l as i128;
    TestResult {
        gt: l > 0xffff_ffff_ffff_ffff,
        ge: l >= 0,
        lt: l < 0,
        le: l <= 0xffff_ffff_ffff_ffff,
        eq: l == 0x1_0000_0000_0000_0000,
        ne: l != 0x1_0000_0000_0000_0000,
    }
}

fn i64_to_u128_gap(l: i64) -> TestResult {
    let l = l as u128;
    TestResult {
        gt: l > 0x1_0000_0000_0000_0000,
        ge: l >= 0x1_0000_0000_0000_0000,
        lt: l < 0x1_0000_0000_0000_0000,
        le: l <= 0x1_0000_0000_0000_0000,
        eq: l == 0x1_0000_0000_0000_0000,
        ne: l != 0x1_0000_0000_0000_0000,
    }
}

fn constant_left(l: u8) -> TestResult {
    let l = l as u32;
    TestResult {
        gt: 420 > l,
        ge: 421 >= l,
        lt: 422 < l,
        le: 423 <= l,
        eq: 424 == l,
        ne: 425 != l,
    }
}
