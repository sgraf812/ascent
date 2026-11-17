import DistilleryTests.Setup.Blocks

/-!
# What `distill_def` unfolds

`distill_def` unfolds a definition only when its `distill [...]` list names it, as `vcgen` does. A rule
for the head of the concrete program, here `wrp_setC` for `setC`, applies at the top of the run.
A definition without a rule, here `setThree`, opens when the list names it.
-/

open Std.WP Lean.Order Distillery Distillery.Blocks
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Blocks.TopLevelRule

distill_def top : BlockM (BitVec 64) Unit from
  ⦃fun _ => True⦄ (setC 3) ⪯[ofStateRepr view] top ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill []

example : top = modifyIf (fun _ => True) fun _ => 3 := rfl

noncomputable def setThree : BlockM CS Unit := setC 3

distill_def three : BlockM (BitVec 64) Unit from
  ⦃fun _ => True⦄ setThree ⪯[ofStateRepr view] three ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [setThree]

example : three = top := rfl

end Distillery.Blocks.TopLevelRule
