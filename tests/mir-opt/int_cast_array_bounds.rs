//@ test-mir-pass: IntCastComparison
//@ skip-filecheck

// EMIT_MIR int_cast_array_bounds.{impl#0}-index.IntCastComparison.diff
struct Array {
    v: [i32; 256]
}

impl Array {
    pub fn index(&self, i: u8) -> i32 {
        self.v[i as usize]
    }
}
