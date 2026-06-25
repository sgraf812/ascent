import Ascent.Corres.Loop

/-!
# While-loop correspondence: a worked example

A sanity check for `corres_whileLoop` (`Ascent.Corres.Loop`): a terminating countdown loop
corresponds to itself.
-/

open Std.Internal.Do Lean.Order Ascent

/-- A terminating countdown loop corresponds to itself: the guards agree, the body corresponds to
itself, and the body strictly decreases the counter (used as the variant). -/
example : Corres (relRef (Eq : Nat → Nat → Prop)) (.eq ⊤ (id : Unit → Unit))
    (whileLoop (fun n => decide (0 < n)) (fun n => pure ((), n - 1)))
    (whileLoop (fun n => decide (0 < n)) (fun n => pure ((), n - 1))) := by
  apply corres_whileLoop (μ := id)
  · intro as cs h; subst h; rfl
  · exact corres_relEq_self _
  · intro E as h _
    simp only [StateT.wp_apply_eq, StateT.run, UB.wp_pure_eq, id]
    have : 0 < as := by simpa using h
    omega
