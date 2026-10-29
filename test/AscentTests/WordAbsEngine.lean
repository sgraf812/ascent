import Ascent.Tactic.VCGen.Frontend
import Ascent.UB

/-!
# Word abstraction through the engine

A chain of `UInt64` additions in `Id` abstracts to a guarded `Int` chain in `UB`, related by
`⌜wordVal · = ·⌝`. Each leaf spec states a fixed return relation, so the engine introduces the
related values as free variables after each step, and the continuation hole of each bind is
applied to the abstract one.
-/

open Std.WP Lean.Order Ascent

namespace WordAbsEngine

def wordVal : UInt64 → Int := fun w => (w.toNat : Int)

/-- Word abstraction: propositional assertions on both sides. -/
abbrev γw : Concretization Prop Prop := Concretization.id Prop

attribute [ascend] wrp_bind

/-- A word constant abstracts to its integer image. -/
@[ascend] theorem pure_word (cv : UInt64) {E : EStack⟨⟩} :
    ⦃(⊤ : Prop)⦄ (pure cv : Id UInt64) ⪯[γw] (pure (wordVal cv) : UB Int)
      ⦃(⌜wordVal · = ·⌝); E⦄ :=
  Refinement.pure_eq (f := wordVal) ⊤ cv rfl

/-- Adding a word abstracts to the guarded integer sum, at the related abstract input. -/
@[ascend] theorem add_word (av : Int) (cv y : UInt64) {E : EStack⟨⟩} :
    ⦃(⌜wordVal cv = av⌝ : Prop)⦄ (pure (cv + y) : Id UInt64)
      ⪯[γw] (UB.guardRet (av + wordVal y < 2 ^ 64) (av + wordVal y)) ⦃(⌜wordVal · = ·⌝); E⦄ := by
  refine Refinement.guardRet _ _ fun hovf hav => ?_
  simp only [CompleteLattice.ofProp_prop_eq] at hav ⊢
  subst hav
  have h : cv.toNat + y.toNat < 2 ^ 64 := by simp only [wordVal] at hovf; omega
  simp only [wordVal, UInt64.toNat_add, Nat.mod_eq_of_lt h]
  omega

/-- Two dependent additions, nested to the left as unfolding a recursive chain produces them. The
run leaves no VC. -/
def chain2 : { a : UB Int //
    ⦃(⊤ : Prop)⦄ ((pure 7 >>= fun r => pure (r + 7)) >>= fun r => pure (r + 7) : Id UInt64)
      ⪯[γw] a ⦃(⌜wordVal · = ·⌝)⦄ } := by
  apply Subtype.mk
  ascend'

/-- Each addition acquires its no-overflow guard, at the abstract value of the previous step. -/
example : chain2.1 = (do
    let a ← (do
      let b ← pure (wordVal 7)
      UB.guardRet (b + wordVal 7 < 2 ^ 64) (b + wordVal 7))
    UB.guardRet (a + wordVal 7 < 2 ^ 64) (a + wordVal 7)) := rfl

end WordAbsEngine
