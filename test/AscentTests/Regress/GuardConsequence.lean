import Ascent.PureRefinement
import Ascent.Tactic.VCGen.Frontend

/-!
# The guard of a value rule against a fixed goal guard

A rule asks for `PureRefinement c ?x True R`, and the only value rule for `c` concludes a guard
stronger than `True`. The solver applies the consequence rule `PureRefinement.weaken_pre`: the
guard becomes the verification condition `True → guard`, and `finish` closes it.
-/

open Std.WP Lean.Order Ascent

namespace GuardConsequence

def wordVal : UInt64 → Int := fun w => (w.toNat : Int)

@[grind =] theorem wordVal_eq (w : UInt64) : wordVal w = (w.toNat : Int) := rfl

abbrev γw : Concretization Prop Prop := Concretization.id Prop

@[ascend_pure] theorem abs_add {a b : UInt64} {x y : Int} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ (FunRel wordVal)) (h₂ : PureRefinement b y P₂ (FunRel wordVal)) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂ ∧ x + y < 2 ^ 64) (FunRel wordVal) := by
  intro ⟨hP₁, hP₂, h⟩
  have ha := h₁ hP₁
  have hb := h₂ hP₂
  simp only [funRel_iff, wordVal] at ha hb h ⊢
  subst ha hb
  have h' : a.toNat + b.toNat < 2 ^ 64 := by omega
  simp only [UInt64.toNat_add, Nat.mod_eq_of_lt h']
  omega

@[ascend_pure low] theorem abs_wordVal {c : UInt64} : PureRefinement c (wordVal c) True (FunRel wordVal) :=
  PureRefinement.funRel

@[ascend high] theorem refines_pure_exact {c : UInt64} {x : Int} {Q : UInt64 → Int → Prop}
    {E : EStack⟨⟩} (_h : PureRefinement c x True (FunRel wordVal)) :
    ⦃Q c x⦄ (pure c : Id UInt64) ⪯[γw] (pure x : UB Int) ⦃Q; E⦄ :=
  (Refinement.pure c x).weaken id

attribute [ascend] wrp_bind

attribute [local grind =] funRel_iff

noncomputable def succ (w : UInt64) : { a : UB Int //
    ⦃w.toNat < 100⦄ (pure (w + 1) : Id UInt64) ⪯[γw] a ⦃(⌜FunRel wordVal · ·⌝)⦄ } := by
  apply Subtype.mk
  ascend with finish

example (w : UInt64) : (succ w).1 = pure (wordVal w + wordVal 1) := rfl

end GuardConsequence
