import Distillery.PureRefinement
import Distillery.Tactic.VCGen.Command

/-!
# Value abstraction through `@[distill_pure]` rules

A chain of `UInt64` additions in `Demonic` abstracts to a guarded `Nat` chain, related by
`FunRel UInt64.toNat`. One rule decomposes an addition, one rule abstracts a closed word, and the
hypothesis of each bind abstracts the bound concrete variable.
-/

open Std.WP Lean.Order Distillery

namespace PureRefinementTest

@[distill_pure] theorem abs_add {a b : UInt64} {x y : Nat} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ (FunRel UInt64.toNat)) (h₂ : PureRefinement b y P₂ (FunRel UInt64.toNat)) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂ ∧ x + y < 2 ^ 64) (FunRel UInt64.toNat) := by
  intro ⟨hP₁, hP₂, h⟩
  have ha := h₁ hP₁
  have hb := h₂ hP₂
  simp only [funRel_iff] at ha hb ⊢
  subst ha hb
  simp only [UInt64.toNat_add, Nat.mod_eq_of_lt h]

@[distill_pure low] theorem abs_toNat {c : UInt64} : PureRefinement c c.toNat True (FunRel UInt64.toNat) :=
  PureRefinement.funRel

attribute [local distill] wrp_bind Refinement.pure_rel

def prog : Demonic UInt64 := do let a ← pure (7 : UInt64); let b ← pure (a + 7); pure (b + 7)

distill_def progN : Demonic Nat from
  ⦃(⊤ : Prop)⦄ prog ⪯[Concretization.id Prop] progN ⦃(⌜FunRel UInt64.toNat · ·⌝)⦄
  distill [prog]

example : ⦃(⊤ : Prop)⦄ prog ⪯[Concretization.id Prop] progN ⦃(⌜FunRel UInt64.toNat · ·⌝)⦄ :=
  progN.refines

-- The precondition and the value of each step are simplified. A power of literals with an exponent
-- above `distill.maxExponent` stays a power.
/--
info: def PureRefinementTest.progN : Demonic Nat :=
do
  let x ←
    do
      Demonic.assert True
      pure 7
  let x ←
    do
      Demonic.assert (x + 7 < 2 ^ 64)
      pure (x + 7)
  Demonic.assert (x + 7 < 2 ^ 64)
  pure (x + 7)
-/
#guard_msgs in
#print progN

def progMul : Demonic UInt64 := do let a ← pure (7 : UInt64); pure (a * 3)

/--
error: distill: no `@[distill_pure]` rule abstracts
  x✝³ * 3
-/
#guard_msgs in
distill_def progMulN : Demonic Nat from
  ⦃(⊤ : Prop)⦄ progMul ⪯[Concretization.id Prop] progMulN ⦃(⌜FunRel UInt64.toNat · ·⌝)⦄
  distill [progMul]

end PureRefinementTest
