import Ascent.Corres.Refinement

/-!
# Scaffold forms of the bind rule

Mid-coupling forms of `Refinement.bind` for hand-written proofs: the head establishes a coupling
and the continuations correspond under it. Derived from the pre-form rule by weakening.
-/

open Std.WP Lean.Order

namespace Ascent

universe u v w w'

variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WPMonad CM CPred CEPred] [WPMonad AM APred AEPred] [WPMonadExact AM APred AEPred]
  [HasEPost CPred APred CEPred AEPred Ξ]
  {γ : Concretization CPred APred CEPred AEPred}
  [Heyting CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
  {c₁ : CM CV} {a₁ : AM AV} {c₂ : CV → CM CV₂} {a₂ : AV → AM AV₂}
  {Q : CV₂ → AV₂ → CPred} {E : Ξ}

/-- The bind rule at a mid coupling: the head establishes `R`, the continuations correspond
under it. -/
theorem Refinement.bind' {R : CV → AV → CPred}
    (h₁ : ⦃P⦄ c₁ ⪯[γ] a₁ ⦃R; E⦄)
    (h₂ : ∀ cv av, ⦃R cv av⦄ (c₂ cv) ⪯[γ] (a₂ av) ⦃Q; E⦄) :
    ⦃P⦄ (c₁ >>= c₂) ⪯[γ] (a₁ >>= a₂) ⦃Q; E⦄ :=
  Refinement.bind.weaken
    (PartialOrder.rel_trans h₁.le_wrp (wrp_mono_post fun cv av => (h₂ cv av).le_wrp))

/-- The bind rule at a functional head coupling: the continuations correspond at each concrete
value and its coupled abstract value. -/
theorem Refinement.bind_eq {f : CV → AV}
    (h₁ : ⦃P⦄ c₁ ⪯[γ] a₁ ⦃fun cv av => ⌜f cv = av⌝; E⦄)
    (h₂ : ∀ cv, ⦃(⊤ : CPred)⦄ (c₂ cv) ⪯[γ] (a₂ (f cv)) ⦃Q; E⦄) :
    ⦃P⦄ (c₁ >>= c₂) ⪯[γ] (a₁ >>= a₂) ⦃Q; E⦄ :=
  .bind' h₁ fun cv av => .of_prop fun h => by rw [← h]; exact h₂ cv

end Ascent
