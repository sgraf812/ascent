import Cases.Setup.State

/-!
# `MatchesJP`

The mirror of the `vcgen` case `MatchesJP`, in `SM Nat`. Each step copies the read state into a mutable variable `x` and updates `x` in each alternative
of three consecutive `match`es on `x` with the literal patterns `0` and `1` and a wildcard. The run
rewrites each `match` into a chain of `dite`s and gives the abstract program one join point for
each `match`. The family stresses the `dite` chain of a `match` before a join point.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.MatchesJP

attribute [distill] wrp_bind wrp_get_SM wrp_set_SM wrp_pure_unit_SM
attribute [distill_pure low] abs_refl
attribute [distill_pure] abs_add abs_eq

def step (v : Nat) : SM Nat Unit := do
  let s ← get
  let mut x := s
  match x with
  | 0 => x := x + v
  | 1 => x := x + (v + 1)
  | _ => x := x + (v + 2)
  match x with
  | 0 => x := x + v
  | 1 => x := x + (v + 1)
  | _ => x := x + (v + 2)
  match x with
  | 0 => x := x + v
  | 1 => x := x + (v + 1)
  | _ => x := x + (v + 2)
  set x

def loop (n : Nat) : SM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

end DistillBench.MatchesJP
