import Cases.Setup.Blocks

/-!
# `Entries`: many entries in the precondition

The concrete state is a register file `Nat → BitVec 64`, and the abstract state is `Unit`. The
precondition relates each register `t i` to an abstract value `vᵢ` by an entry
`PureRefinement (t i) vᵢ True Eq`. The concrete program reads the sum of `n` registers at the end,
and the rule `wrp_peek` asks the value solver for its abstract value, `v₀ + … + vₙ₋₁`. The family
stresses the lookup of `n` entries in the environment of the value solver. The `vcgen` case
`RegFile` keeps registers in the state, and this family turns them into values of the abstract
program, as the register step `Demo.Regs` of the demo does.
-/

open Std.WP Lean.Order Distillery DistillBench.Blocks
open Distillery.Concretization (ofStateRepr)

namespace DistillBench.Entries

abbrev RF := Nat → BitVec 64

def unitView (_ : RF) : Unit := ()

@[distill] theorem wrp_peek {Q : BitVec 64 → BitVec 64 → RF → Prop}
    {E : (Lbl → Lbl → RF → Prop) × EStack⟨⟩} (c : RF → BitVec 64) (b : BitVec 64) :
    (fun t => PureRefinement (c t) b True Eq ∧ Q (c t) b t)
      ⊑ wrp (ofStateRepr unitView) (peek c) (pure b : BlockM Unit (BitVec 64)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred,
    WPMonadExact.wp_pure_eq] at ht
  obtain ⟨⟨-, hq⟩, hqa⟩ := ht
  rw [wp_peek, Concretization.post_pi]
  exact ⟨b, hq, hqa⟩

theorem abs_add {a b x y : BitVec 64} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂) Eq := fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

attribute [distill_pure] abs_add

end DistillBench.Entries
