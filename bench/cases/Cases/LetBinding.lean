import Cases.Setup.State

/-!
# `LetBinding`

The mirror of the `vcgen` case `LetBinding`, in `SM Nat`. Each step binds the pure value `offset := v + 1` and uses it in two writes. The run gives the
abstract program the binding of the abstract value. The family stresses the abstraction of a
`have` into a `have`.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.LetBinding

attribute [distill] wrp_bind wrp_get_SM wrp_set_SM wrp_pure_unit_SM
attribute [distill_pure low] abs_refl
attribute [distill_pure] abs_add abs_sub

def step (v : Nat) : SM Nat Unit := do
  let s ← get
  let offset := v + 1
  set (s + offset)
  let s ← get
  set (s - offset)

def loop (n : Nat) : SM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

end DistillBench.LetBinding
