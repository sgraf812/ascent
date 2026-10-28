import Ascent.Refinement

/-!
# Scaffold forms of the bind rule

Forms of `Refinement.bind` with an intermediate return relation for hand-written proofs: the
head establishes a return relation and the continuations correspond under it. Derived from the pre-form rule by weakening.
-/

open Std.WP Lean.Order

namespace Ascent

universe u v w w'

variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPosts AEPosts : Type w'}
  {ERels : Type u}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WPMonad CM CPred CEPosts] [WPMonad AM APred AEPosts] [WPMonadExact AM APred AEPosts]
  [EPostsConcretization CPred APred CEPosts AEPosts ERels]
  {γ : Concretization CPred APred}
  [Heyting CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
  {c₁ : CM CV} {a₁ : AM AV} {c₂ : CV → CM CV₂} {a₂ : AV → AM AV₂}
  {Q : CV₂ → AV₂ → CPred} {E : ERels}

/-- The bind rule at an intermediate return relation: the head establishes `R`, the
continuations correspond under it. -/
theorem Refinement.bind' {R : CV → AV → CPred}
    (h₁ : ⦃P⦄ c₁ ⪯[γ] a₁ ⦃R; E⦄)
    (h₂ : ∀ cv av, ⦃R cv av⦄ (c₂ cv) ⪯[γ] (a₂ av) ⦃Q; E⦄) :
    ⦃P⦄ (c₁ >>= c₂) ⪯[γ] (a₁ >>= a₂) ⦃Q; E⦄ :=
  Refinement.bind.weaken
    (PartialOrder.rel_trans h₁.le_wrp (wrp_mono_post fun cv av => (h₂ cv av).le_wrp))

/-- The bind rule at a functional head return relation: the continuations correspond at each
concrete value and its related abstract value. -/
theorem Refinement.bind_eq {f : CV → AV}
    (h₁ : ⦃P⦄ c₁ ⪯[γ] a₁ ⦃fun cv av => ⌜f cv = av⌝; E⦄)
    (h₂ : ∀ cv, ⦃(⊤ : CPred)⦄ (c₂ cv) ⪯[γ] (a₂ (f cv)) ⦃Q; E⦄) :
    ⦃P⦄ (c₁ >>= c₂) ⪯[γ] (a₁ >>= a₂) ⦃Q; E⦄ :=
  .bind' h₁ fun cv av => .of_prop fun h => by rw [← h]; exact h₂ cv

end Ascent
