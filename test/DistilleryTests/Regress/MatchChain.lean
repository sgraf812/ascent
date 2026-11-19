import DistilleryTests.Regress.StateSplit

/-!
# A match on a value from the state becomes a chain of `if`s

The program `progLit` reads the state into `s` and matches `s` against the literals `0` and `1`,
with a final variable pattern `m`. The run rewrites the `match` into the chain
`if h : s = 0 then … else if h : s = 1 then … else …`, and the value solver abstracts each
condition `s = k` to `x = k`. The abstract program is the same chain on `x`, and its last branch
refines the alternative of `m` at `x`. The program `progBool` matches `s == 3` against `true` and
`false`, without a variable pattern: the alternative of `false` is the last `else`. The test pins
the deviation "two-sided split" of `docs/vcgen-fork.md`.
-/

open Std.WP Lean.Order Distillery StateSplitTest

namespace MatchChainTest

@[distill_pure] theorem abs_eq {α : Type} {a b x y : α} {P₁ P₂ : Prop} (h₁ : PureRefinement a x P₁ Eq)
    (h₂ : PureRefinement b y P₂ Eq) : PureRefinement (a = b) (x = y) (P₁ ∧ P₂) Eq :=
  fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

attribute [local distill] wrp_bind

def progLit : SM Nat Unit := do
  let s ← get
  match s with
  | 0 => set 5
  | 1 => set 7
  | m => set (m - 1)

distill_def progLitA : SM Nat Unit from
  ⦃fun _ => True⦄ progLit ⪯[γ Nat] progLitA ⦃fun _ _ _ => True⦄
  distill [progLit]

/--
info: def MatchChainTest.progLitA : SM Nat Unit :=
do
  let x ← get
  if h : x = 0 then set 5 else if h : x = 1 then set 7 else set (x - 1)
-/
#guard_msgs in
#print progLitA

@[distill_pure] theorem abs_beq {a b x y : Nat} {P₁ P₂ : Prop} (h₁ : PureRefinement a x P₁ Eq)
    (h₂ : PureRefinement b y P₂ Eq) : PureRefinement (a == b) (x == y) (P₁ ∧ P₂) Eq :=
  fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

def progBool : SM Nat Unit := do
  let s ← get
  match s == 3 with
  | true => set 5
  | false => set s

distill_def progBoolA : SM Nat Unit from
  ⦃fun _ => True⦄ progBool ⪯[γ Nat] progBoolA ⦃fun _ _ _ => True⦄
  distill [progBool]

/--
info: def MatchChainTest.progBoolA : SM Nat Unit :=
do
  let x ← get
  if h : (x == 3) = true then set 5 else set x
-/
#guard_msgs in
#print progBoolA

end MatchChainTest
