import AscentTests.Setup.Blocks
import Ascent.Refinement.Catch

/-!
# The exit catch at the top of a chain

`catchExit e b` returns where `b` throws `e`. `Refinement.transport_catchExit` turns a triple about
the caught abstract program into a triple about the concrete program, whose exception postcondition
at `e` is the return postcondition of the caught program. Here the abstract program comes from
`ascend_def`, and the triple about the caught program from `wp_catchExit`.
-/

open Std.WP Lean.Order Ascent Ascent.Blocks
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Blocks.CatchExit

ascend_def top : BlockM (BitVec 64) Unit from
  ⦃fun _ => True⦄ (setC 3) ⪯[ofStateRepr view] top ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend []

theorem top_caught : Triple (catchExit Lbl.exit top) (fun _ => True) (fun _ v => v = 3)
    (fun _ _ => False, estack⟨⟩) :=
  ⟨fun s _ => by
    rw [wp_catchExit, show top = modifyIf (fun _ => True) (fun _ => 3) from rfl, wp_modifyIf]
    exact ⟨trivial, rfl⟩⟩

example : Triple (setC 3) (fun _ => True) (fun _ s => s.r = 3)
    (fun l s => l = Lbl.exit ∧ s.r = 3, estack⟨⟩) := by
  have h := Refinement.transport_catchExit (e := Lbl.exit) top.refines top_caught
  refine ⟨fun s hs => WP.wp_monotone (x := setC 3) ?_ ?_ s (h.le_wp s (by grind))⟩
  · intro _ t ht
    simp only [Concretization.post_pi, ofStateRepr_pred] at ht
    grind [view]
  · refine Prod.mk_le _ _ _ (fun l t ht => ?_) PartialOrder.rel_refl
    simp only [Concretization.post_pi, ofStateRepr_pred] at ht
    grind [view]

end Ascent.Blocks.CatchExit
