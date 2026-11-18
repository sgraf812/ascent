import Cases.Setup.State

/-!
# `PurePrecond`: specs with a fixed pre- and postcondition

The mirror of the `vcgen` case `PurePrecond`, in `SM Bool`. The step `flipp b` negates the state.
Its two specs are `Refinement` theorems with a fixed precondition on the state (`s = true` or
`s = false`) and a fixed return relation, so that each application weakens the spec to the goal:
the postcondition `s = false` of `flipp true` establishes the precondition of `flipp false`. The
family stresses the rule construction for `Refinement` specs with a fixed pre- and postcondition.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.PurePrecond

def flipp (_ : Bool) : SM Bool Unit := modify not

theorem wp_flipp (b : Bool) (Q : Unit → Bool → Prop) (E : EStack⟨⟩) (s : Bool) :
    wp (flipp b) Q E s = Q () (!s) := rfl

theorem flipp_spec (b : Bool) :
    ⦃fun s => s = b⦄ (flipp b) ⪯[γ Bool] (flipp b) ⦃fun _ _ s => s = !b⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_flipp] at h ⊢
  rw [Concretization.post_pi]
  exact ⟨(), by rw [h.1], h.2⟩

@[distill] theorem flipp_true : ⦃fun s => s = true⦄ (flipp true) ⪯[γ Bool] (flipp true)
    ⦃fun _ _ s => s = false⦄ := flipp_spec true

@[distill] theorem flipp_false : ⦃fun s => s = false⦄ (flipp false) ⪯[γ Bool] (flipp false)
    ⦃fun _ _ s => s = true⦄ := flipp_spec false

attribute [distill] wrp_bind wrp_pure_unit_SM

def step : SM Bool Unit := do
  flipp true
  flipp false

def loop (n : Nat) : SM Bool Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

end DistillBench.PurePrecond
