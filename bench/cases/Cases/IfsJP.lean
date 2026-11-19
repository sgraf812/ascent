import Cases.Setup.State

/-!
# `IfsJP`

The mirror of the `vcgen` case `IfsJP`, in `SM Nat`. Each step copies the read state into a mutable variable `x` and updates `x` in both branches of
three consecutive `if`s on `x`. The do-elaborator shares the code after each `if` through a join
point, and the run gives the abstract program one join point for each. The family stresses the
abstract join point, the abstraction of a `have` into a `have`, and the split on a condition after a
join point.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.IfsJP

attribute [distill] wrp_bind wrp_get_SM wrp_set_SM wrp_pure_unit_SM
attribute [distill_pure low] abs_refl
attribute [distill_pure] abs_add abs_gt

def step (v : Nat) : SM Nat Unit := do
  let s ← get
  let mut x := s
  if x > 0 then x := x + v else x := x + (v + 1)
  if x > 1 then x := x + v else x := x + (v + 1)
  if x > 2 then x := x + v else x := x + (v + 1)
  set x

def loop (n : Nat) : SM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

end DistillBench.IfsJP
