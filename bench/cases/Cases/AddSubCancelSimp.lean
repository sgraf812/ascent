import Cases.Setup.State

/-!
# `AddSubCancelSimp`: rules of the invocation

The mirror of the `vcgen` case `AddSubCancelSimp`, which runs the program of `AddSubCancel` with
specs outside the spec database. The rules for `get`, `set` and `pure ()` carry no `@[distill]`
attribute in this module. The run passes them in its `distill [...]` list, so the engine builds a spec of the
invocation from each term. The family stresses the rules of the invocation on the chain of
`AddSubCancel`.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.AddSubCancelSimp

attribute [distill] wrp_bind
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

end DistillBench.AddSubCancelSimp
