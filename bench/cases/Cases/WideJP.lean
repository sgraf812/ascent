import Cases.Setup.State

/-!
# `WideJP`

The mirror of the `vcgen` case `WideJP`, in `SM Nat`. `chain n x` unfolds to `n` nested `if`s, and
the code of `wide n` after `chain n x` is a join point that each of the `n + 1` results of
`chain n x` jumps to. The rule `wrp_pure_var_SM` gives the
continuation of `chain n x` a variable for the result, so that the `n + 1` results share one abstract
continuation. The family stresses an abstract join point with many jumps.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.WideJP

attribute [distill] wrp_bind wrp_get_SM wrp_set_SM wrp_pure_unit_SM wrp_pure_var_SM
attribute [distill_pure low] abs_refl
attribute [distill_pure] abs_add abs_eq abs_lt

def chain : Nat → Nat → SM Nat Nat
  | 0, _ => pure 1
  | n+1, x => if x = n then pure (n + 2) else chain n x

def wide (n : Nat) : SM Nat Nat := do
  let x ← get
  let mut y := 0
  if x < n then y ← chain n x
  return y + 1

end DistillBench.WideJP
