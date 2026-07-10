import Ascent.Corres.RTriple

/-!
# Support lemmas applied by the ascend engine

Decomposition rules for spec preconditions at the `Prop` lattice, where `⊑` is implication.
The engine applies these as backward steps when a registered spec's precondition surfaces as
the right-hand side of an entailment goal.
-/

open Lean.Order

namespace Ascend

/-- Split a conjunction on the right of an entailment. -/
theorem prop_le_and {P A B : Prop} (h₁ : P ⊑ A) (h₂ : P ⊑ B) : P ⊑ (A ∧ B : Prop) :=
  fun hP => ⟨h₁ hP, h₂ hP⟩

/-- Introduce the hypothesis of an implication on the right of an entailment. -/
theorem prop_le_imp {P A B : Prop} (h : A → P ⊑ B) : P ⊑ (A → B) :=
  fun hP hA => h hA hP

/-- Close a reflexive equation on the right of an entailment. -/
theorem prop_le_eq_refl {P : Prop} {α : Sort u} (a : α) : P ⊑ (a = a) :=
  fun _ => rfl

/-- Close an entailment against a proof of the right-hand side, such as an established
coupling hypothesis. -/
theorem prop_le_of {P A : Prop} (h : A) : P ⊑ A :=
  fun _ => h

end Ascend
