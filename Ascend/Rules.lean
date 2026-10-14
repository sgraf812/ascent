import Ascent.Corres.Refinement

/-!
# Support lemmas applied by the ascend engine

Decomposition rules for spec preconditions at the `Prop` lattice, where `⊑` is implication.
The engine applies these as backward steps when a registered spec's precondition surfaces as
the right-hand side of an entailment goal.
-/

open Std.WP Lean.Order

namespace Ascend

/-- Split a conjunction on the right of an entailment. -/
theorem prop_le_and {P A B : Prop} (h₁ : P ⊑ A) (h₂ : P ⊑ B) : P ⊑ (A ∧ B : Prop) :=
  fun hP => ⟨h₁ hP, h₂ hP⟩

/-- Introduce the hypothesis of an implication on the right of an entailment. -/
theorem prop_le_imp {P A B : Prop} (h : A → P ⊑ B) : P ⊑ (A → B) :=
  fun hP hA => h hA hP

end Ascend
