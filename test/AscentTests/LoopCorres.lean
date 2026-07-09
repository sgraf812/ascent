import Ascent.Corres.Loop

/-!
# While-loop simulation: a worked example

A sanity check for `sim_whileLoop` (`Ascent.Corres.Loop`): a terminating countdown loop
simulates itself.
-/

open Std.Internal.Do Lean.Order Ascent

/-- A terminating countdown loop simulates itself: the guards agree, the body simulates itself,
and the body strictly decreases the counter (used as the variant). -/
example : ⦃(⊤ : Nat → Prop)⦄
    (whileLoop (fun n => decide (0 < n)) (fun n => pure ((), n - 1)))
    ⊑[relRef (Eq : Nat → Nat → Prop)]
    (whileLoop (fun n => decide (0 < n)) (fun n => pure ((), n - 1)))
    ⦃fun _ _ => ⊤; ()⦄ := by
  apply sim_whileLoop (μ := id)
  · intro as cs h; subst h; rfl
  · exact (sim_relEq_self _ _).mono_post fun _ _ => le_top _
  · intro E as h _
    simp only [StateT.wp_apply_eq, StateT.run, UB.wp_pure_eq, id]
    have : 0 < as := by simpa using h
    omega
