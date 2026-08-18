import Ascent.Corres.Loop

/-!
# While-loop refinement: a worked example

A sanity check for `refines_whileLoop` (`Ascent.Corres.Loop`): a terminating countdown loop
refines itself.
-/

open Std.WP Lean.Order Ascent

/-- A terminating countdown loop refines itself: the guards agree, the body refines itself,
and the body strictly decreases the counter (used as the variant). -/
example : ⦃(⊤ : Nat → Prop)⦄
    (whileLoop (fun n => decide (0 < n)) (fun n => pure ((), n - 1)))
    ⊑[relRef (Eq : Nat → Nat → Prop)]
    (whileLoop (fun n => decide (0 < n)) (fun n => pure ((), n - 1)))
    ⦃fun _ _ => ⊤⦄ := by
  apply refines_whileLoop (μ := id)
  · intro as cs h; subst h; rfl
  · exact (refines_relEq_self _ _).mono_post fun _ _ => le_top _
  · intro E as h _
    simp only [StateT.wp_apply_eq, StateT.run, UB.wp_pure_eq, id]
    have : 0 < as := by simpa using h
    omega
