import Ascent.Demonic

/-!
# `wp` lemmas for `StateT σ Demonic`

`bind` pointwise in the state, the conjunction of two postconditions, and `StateT.assume g`, which
continues if the state satisfies `g` and fails otherwise.
-/

open Std.WP Lean.Order Ascent

theorem wp_bind_StateT {σ α β} (x : StateT σ Demonic α) (f : α → StateT σ Demonic β)
    (Q : β → σ → Prop) (E : EStack⟨⟩) (s : σ) :
    wp (x >>= f) Q E s = wp x (fun a s' => wp (f a) Q E s') E s := by
  simp only [StateT.wp_apply_eq, StateT.run_bind, Demonic.wp_bind_eq]

theorem wp_and_StateT {σ α} (x : StateT σ Demonic α) (P R : α → σ → Prop) (E : EStack⟨⟩) (s : σ)
    (hP : wp x P E s) (hR : wp x R E s) : wp x (fun a s' => P a s' ∧ R a s') E s := by
  rw [StateT.wp_apply_eq] at hP hR ⊢
  exact Demonic.wp_and (x.run s) (fun p => P p.1 p.2) (fun p => R p.1 p.2) E hP hR



noncomputable def StateT.assume {σ : Type} (g : σ → Prop) : StateT σ Demonic PUnit := do
  Demonic.assume (g (← get))

theorem StateT.wp_assume_eq {σ : Type} (g : σ → Prop) (Q : PUnit → σ → Prop) (E : EStack⟨⟩) (s : σ) :
    wp (StateT.assume g) Q E s = (g s ∧ Q () s) := by
  simp only [StateT.assume, StateT.wp_apply_eq, StateT.run_bind, StateT.run_get, liftM, monadLift,
    MonadLift.monadLift, StateT.run_lift, Demonic.wp_bind_eq, Demonic.wp_pure_eq, Demonic.wp_assume_eq]

@[spec] theorem StateT.Spec.assume {σ : Type} (g : σ → Prop) (Q : PUnit → σ → Prop) (E : EStack⟨⟩) :
    ⦃fun s => g s ∧ Q () s⦄ StateT.assume g ⦃Q; E⦄ :=
  ⟨fun s h => by rw [StateT.wp_assume_eq]; exact h⟩

theorem ExceptT.wp_monadLift_StateT_Demonic {ε σ α : Type} (x : StateT σ Demonic α) (Q : α → σ → Prop)
    (E : (ε → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (monadLift x : ExceptT ε (StateT σ Demonic) α) Q E s = wp x Q E.2 s := by
  simp only [ExceptT.wp_apply_eq, StateT.wp_apply_eq, monadLift, MonadLift.monadLift,
    ExceptT.run_lift, StateT.run_map, Demonic.wp_map_eq]
  rfl
