import Ascent.Refinement.WhileLoop

/-!
# While-loop refinement: a worked example

A sanity check for `refines_whileLoop` (`Ascent.Refinement.WhileLoop`): a countdown loop
refines itself.
-/

open Std.WP Lean.Order Ascent

/-- A countdown loop refines itself: the guards agree, and the body refines itself. -/
example : ⦃(⊤ : Nat → Prop)⦄
    (whileLoop (fun n => decide (0 < n)) (fun n => pure ((), n - 1)))
    ⪯[Concretization.ofStateRel (Eq : Nat → Nat → Prop)]
    (whileLoop (fun n => decide (0 < n)) (fun n => pure ((), n - 1)))
    ⦃fun _ _ => ⊤⦄ := by
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
