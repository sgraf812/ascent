import Ascent.PureRefinement
import Ascent.Tactic.VCGen.Command

/-!
# Value abstraction through `@[ascend_pure]` rules

A chain of `UInt64` additions in `UB` abstracts to a guarded `Nat` chain, related by
`FunRel UInt64.toNat`. One rule decomposes an addition, one rule abstracts a closed word, and the
hypothesis of each bind abstracts the bound concrete variable.
-/

open Std.WP Lean.Order Ascent

namespace PureRefinementTest

@[ascend_pure] theorem abs_add {a b : UInt64} {x y : Nat} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ (FunRel UInt64.toNat)) (h₂ : PureRefinement b y P₂ (FunRel UInt64.toNat)) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂ ∧ x + y < 2 ^ 64) (FunRel UInt64.toNat) := by
  intro ⟨hP₁, hP₂, h⟩
  have ha := h₁ hP₁
  have hb := h₂ hP₂
  simp only [funRel_iff] at ha hb ⊢
  subst ha hb
  simp only [UInt64.toNat_add, Nat.mod_eq_of_lt h]

@[ascend_pure low] theorem abs_toNat {c : UInt64} : PureRefinement c c.toNat True (FunRel UInt64.toNat) :=
  PureRefinement.funRel

attribute [local ascend] wrp_bind Refinement.pure_rel

def prog : UB UInt64 := do let a ← pure (7 : UInt64); let b ← pure (a + 7); pure (b + 7)

ascend_def progN : UB Nat from
  ⦃(⊤ : Prop)⦄ prog ⪯[Concretization.id Prop] progN ⦃(⌜FunRel UInt64.toNat · ·⌝)⦄

example : ⦃(⊤ : Prop)⦄ prog ⪯[Concretization.id Prop] progN ⦃(⌜FunRel UInt64.toNat · ·⌝)⦄ :=
  progN.refines

-- The precondition and the value of each step are simplified. A power of literals with an exponent
-- above `ascend.maxExponent` stays a power.
/--
info: def PureRefinementTest.progN : UB Nat :=
do
  let x ←
    do
      UB.assume True
      pure 7
  let x ←
    do
      UB.assume (x + 7 < 2 ^ 64)
      pure (x + 7)
  UB.assume (x + 7 < 2 ^ 64)
  pure (x + 7)
-/
#guard_msgs in
#print progN

def progMul : UB UInt64 := do let a ← pure (7 : UInt64); pure (a * 3)

/--
error: ascend: no `@[ascend_pure]` rule abstracts
  x✝³ * 3
-/
#guard_msgs in
ascend_def progMulN : UB Nat from
  ⦃(⊤ : Prop)⦄ progMul ⪯[Concretization.id Prop] progMulN ⦃(⌜FunRel UInt64.toNat · ·⌝)⦄

end PureRefinementTest
