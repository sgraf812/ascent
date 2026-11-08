import AscentTests.Setup.Blocks

/-!
# A rule for the head of the concrete program at the top of a run

`ascend_def` unfolds the head constant of its concrete program when no rule refines it. A rule for
the head, here `wrp_setC` for `setC`, applies at the top of the run, where the unfold equations of
the head ranked above it and the run continued with the unfolded body.
-/

open Std.WP Lean.Order Ascent Ascent.Blocks
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Blocks.TopLevelRule

ascend_def top : BlockM (BitVec 64) Unit from
  ⦃fun _ => True⦄ (setC 3) ⪯[ofStateRepr view] top ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend []

example : top = modifyIf (fun _ => True) fun _ => 3 := rfl

end Ascent.Blocks.TopLevelRule
