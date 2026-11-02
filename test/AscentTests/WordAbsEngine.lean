import Ascent.PureRefinement
import Ascent.Tactic.VCGen.Frontend

/-!
# Word abstraction through the engine

A chain of `UInt64` additions in `Id` abstracts to a guarded `Int` chain in `UB`, related by
`FunRel wordVal`. `Refinement.pure_rel` abstracts each `pure`, the `@[ascend_pure]` rules below
abstract the value inside it, and each bind relates the concrete and the abstract variable.
-/

open Std.WP Lean.Order Ascent

namespace WordAbsEngine

def wordVal : UInt64 → Int := fun w => (w.toNat : Int)

/-- Word abstraction: propositional assertions on both sides. -/
abbrev γw : Concretization Prop Prop := Concretization.id Prop

attribute [ascend] wrp_bind Refinement.pure_rel

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

/-- Two dependent additions, nested to the left as unfolding a recursive chain produces them. The
run leaves no VC. -/
noncomputable def chain2 : { a : UB Int //
    ⦃(⊤ : Prop)⦄ ((pure 7 >>= fun r => pure (r + 7)) >>= fun r => pure (r + 7) : Id UInt64)
      ⪯[γw] a ⦃(⌜FunRel wordVal · ·⌝)⦄ } := by
  apply Subtype.mk
  ascend'

/-- Each addition acquires its no-overflow guard, at the abstract value of the previous step. -/
example : chain2.1 = (do
    let a ← (do
      let b ← UB.guardRet True (wordVal 7)
      UB.guardRet (b + wordVal 7 < 2 ^ 64) (b + wordVal 7))
    UB.guardRet (a + wordVal 7 < 2 ^ 64) (a + wordVal 7)) := rfl

end WordAbsEngine
