import Ascent.Refinement.WhileLoop

/-!
# While-loop refinement: a worked example

A sanity check for `refines_whileLoop` (`Ascent.Refinement.WhileLoop`): a countdown loop
refines itself. `Refinement.transport` then moves the abstract specification of the countdown to
the concrete countdown.
-/

open Std.WP Lean.Order Ascent

/-- Counts the state down to `0`. -/
def countdown : StateT Nat UB Unit :=
  whileLoop (fun n => decide (0 < n)) (fun n => pure ((), n - 1))

/-- A countdown loop refines itself: the guards agree, and the body refines itself. -/
theorem countdown_refines : ⦃(⊤ : Nat → Prop)⦄ countdown
    ⪯[Concretization.ofStateRel (Eq : Nat → Nat → Prop)] countdown ⦃fun _ _ => ⊤⦄ := by
  apply refines_whileLoop
  · intro as cs h; subst h; rfl
  · exact (refines_relEq_self _ _).mono_post fun _ _ => le_top _

/-- A loop that never terminates refines itself. -/
example : ⦃(⊤ : Nat → Prop)⦄
    (whileLoop (fun _ => true) (fun n => pure ((), n)))
    ⪯[Concretization.ofStateRel (Eq : Nat → Nat → Prop)]
    (whileLoop (fun _ => true) (fun n => pure ((), n)))
    ⦃fun _ _ => ⊤⦄ := by
  apply refines_whileLoop
  · intro as cs h; subst h; rfl
  · exact (refines_relEq_self _ _).mono_post fun _ _ => le_top _

theorem countdown_spec : Triple countdown (⊤ : Nat → Prop) (fun _ n => n = 0) ⊥ := by
  refine ⟨fun n _ => ?_⟩
  induction n with
  | zero => rw [countdown, wp_whileLoop]; rfl
  | succ n ih =>
    rw [countdown, wp_whileLoop, ite_eq_left (by simp)]
    simpa [countdown, StateT.wp_apply_eq, StateT.run, UB.wp_pure_eq] using ih

/-- The abstract specification transports to the concrete countdown. -/
example : Triple countdown (⊤ : Nat → Prop) (fun _ n => n = 0) ⊥ := by
  have h := countdown_refines.transport countdown_spec
  refine ⟨fun n _ => ?_⟩
  have hn := h.le_wp n (by simp [Concretization.ofStateRel_pred])
  rw [Concretization.ofStateRel_post_top] at hn
  refine WP.wp_monotone (x := countdown) ?_ ?_ n hn
  · rintro _ cs ⟨_, as, rfl, h0⟩
    exact h0
  · exact PartialOrder.rel_refl
