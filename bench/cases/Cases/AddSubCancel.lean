import Cases.Setup.State

/-!
# `AddSubCancel`: get and set in a state monad

The mirror of the `vcgen` case `AddSubCancel`. The concrete program `loop n` runs `n` steps in
`SM Nat`, and each step adds a value to the state and subtracts it again. The abstract program is
the same loop under `Concretization.id`. Each `get` binds an abstract variable of the abstract
program, and each `set` asks the value solver for the abstract value of the written state. The
family stresses `wrp_bind`, the continuation holes and the value solver on a long chain of binds.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.AddSubCancel

attribute [distill] wrp_bind wrp_get_SM wrp_set_SM wrp_pure_unit_SM
attribute [distill_pure low] abs_refl
attribute [distill_pure] abs_add abs_sub

def step (v : Nat) : SM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : SM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

end DistillBench.AddSubCancel
