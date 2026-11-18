import Cases.Setup.State

/-!
# `MatchIota`: a `match` on a literal

The mirror of the `vcgen` case `MatchIota`, in `EM Nat`. Each step matches on its literal argument
`v`: the case `0` throws, and the case `n + 1` adds and subtracts. The `match` reduces on the literal,
so the run splits nothing. The family stresses the reduction of a matcher on the concrete side and
the exception relation at the final `throw`.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.MatchIota

attribute [distill] wrp_bind wrp_get_EM wrp_set_EM wrp_throw_EM wrp_pure_unit_EM
attribute [distill_pure low] abs_refl
attribute [distill_pure] abs_add abs_sub

def step (v : Nat) : EM Nat Unit := do
  let s ← get
  match v with
  | 0 => throw "v is zero"
  | n+1 => set (s + n + 1); let s ← get; set (s - n)

def loop (n : Nat) : EM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

end DistillBench.MatchIota
