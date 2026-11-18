import Distillery.PureRefinement
import Distillery.Tactic.VCGen.Command

/-!
# `Holes`: a continuation over many variables

The concrete program in `Demonic Nat` binds `n` values `x₁, …, xₙ` and returns their sum. The rule
`Refinement.pure_rel` abstracts each `pure` and binds an abstract variable, so the continuation hole
of the `k`-th bind is a hole under the `k` variables before it, and the last step abstracts a sum of
`n` variables. The family stresses the delayed assignment of continuation holes in a growing
context and the value solver on a wide term. No `vcgen` case corresponds to this family.
-/

open Std.WP Lean.Order Distillery

namespace DistillBench.Holes

abbrev γp : Concretization Prop Prop := Concretization.id Prop

attribute [distill] wrp_bind Refinement.pure_rel

theorem abs_refl {α : Type} {c : α} : PureRefinement c c True Eq := fun _ => rfl

theorem abs_add {a b x y : Nat} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂) Eq := fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

attribute [distill_pure low] abs_refl
attribute [distill_pure] abs_add

end DistillBench.Holes
