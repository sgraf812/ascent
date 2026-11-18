import Cases.Setup.State

/-!
# `MatchSplit`: a `match` on a value read from the state

The mirror of the `vcgen` case `MatchSplit`, in `EM Nat`. Each step reads the state into `s` and
matches on it: the case `0` throws, and the case `n + 1` writes `n`. The run abstracts the
discriminant to the abstract read value and splits both programs into the two alternatives. The
family stresses the abstraction of a discriminant and the two-sided split of a matcher.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.MatchSplit

attribute [distill] wrp_bind wrp_get_EM wrp_set_EM wrp_throw_EM wrp_pure_unit_EM
attribute [distill_pure low] abs_refl

def step : EM Nat Unit := do
  let s ← get
  match s with
  | 0 => throw "s is zero"
  | n+1 => set n

def loop (n : Nat) : EM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

end DistillBench.MatchSplit
