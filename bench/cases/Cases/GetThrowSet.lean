import Cases.Setup.State

/-!
# `GetThrowSet`: a conditional throw on the state

The mirror of the `vcgen` case `GetThrowSet`, in `EM Nat := ExceptT String (StateT Nat Demonic)`.
Each step reads the state `s`, throws by `throwIf (Nat.blt lim s) …` when `s` exceeds the limit
`lim`, and else increments the state. The rule `wrp_throwIf_EM` asks the value solver for the
abstract condition, so the abstract program branches on an abstract value. The family stresses the
exception relation of `ExceptT` and a branch of each step on an abstracted condition.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.GetThrowSet

attribute [distill] wrp_bind wrp_get_EM wrp_set_EM wrp_throwIf_EM wrp_pure_unit_EM
attribute [distill_pure low] abs_refl
attribute [distill_pure] abs_add abs_blt

def step (lim : Nat) : EM Nat Unit := do
  let s ← get
  throwIf (Nat.blt lim s) "s is too large"
  set (s + 1)

def loop (n : Nat) : EM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => loop n; step n

end DistillBench.GetThrowSet
