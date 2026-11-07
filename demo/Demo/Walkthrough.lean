import Demo.ZipPure

/-!
# From x64 to `Array.zipWith`

The C function

```c
void zipWithAdd(const long *a, const long *b, long *out, long n) {
  for (long i = 0; i < n; i++)
    out[i] = a[i] + b[i];
}
```

compiled by clang with `-O1 -fno-vectorize -fno-unroll-loops` is the kraken program `zipWithAdd`.
Each section below is one refinement, from the machine code to the pure program.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

namespace Ascent.Kraken.Walkthrough

/-! ## 1. The x64 text -/

#print zipWithAdd

/-! ## 2. Blocks, synthesized by `ascend_def`

`zipWithAddA` is a loop over the blocks of the text, one guarded step per instruction, with the flags
cleared and `cmp; jcc` fused into one branch. Each step is a register write `setReg64`, a load into a
register `loadReg8`, or a store `storeWord8`. `ascend_def` synthesized it and proved: -/

#check @zipWithAddA.refines

/-! ## 3. A structured loop, by rewriting

`sym_simp_def` rewrites the block loop of `zipWithAddA` into an `if` and a `repeat'` loop over the
machine state: the jump of the loop block to itself becomes `continue`, and the return ends the
program in both branches. The command proves
the equation `zipWithAddT.eq`, so the first refinement carries over to `zipWithAddT`: -/

#print zipWithAddT
#check @zipWithAddT.refines

/-! ## 4. Registers as values, synthesized by `ascend_def`

The state is the data memory alone. The lifting relation, the one hint of the run, is
`RegsRel [(.rdi, rdi), …, (.rax, rax)]`: it names the registers that become values. `rdi`, `rsi`,
`rdx`, `rcx` and `rsp` are parameters, and `rax` is the value of the loop. The loaded values of
`r8` become variables. `ascend_def` synthesized `zipWithAddL₀`, and `sym_simp_def` states its
branch conditions as comparisons of the values in `zipWithAddL`: -/

#print zipWithAddL
#check @zipWithAddL.refines

/-! ## 5. Arrays, synthesized by `ascend_def`

The state is the output array. The input arrays are parameters, named by their base addresses, and
the loads and the store become array reads and an array update. The relation of the loop, the hint
of the run, states the layout `ArrayLayout [(A, a), (B, b)] O n [rsp]` of the memory: the input
arrays, the written array, and the return slot. `ascend_def` synthesized `zipWithAddArr₀`, and
`sym_simp_def` puts the array reads in place in `zipWithAddArr`: -/

#print zipWithAddArr
#check @zipWithAddArr.refines

/-! ## 6. The pure program

`vcgen` proves that the array program exits with `Array.zipWith (· + ·)` of its inputs, from a loop
invariant and a measure. So the array program refines the pure program. -/

#check @zipWithAddArr_spec
#print zipWithAddP
#check @zipWithAddArr_refines_P

/-! ## 7. Back to the machine code

The refinements carry the result of the pure program back to the x64 text. -/

#check @zipWithAdd_correct
#print axioms zipWithAdd_correct

end Ascent.Kraken.Walkthrough
