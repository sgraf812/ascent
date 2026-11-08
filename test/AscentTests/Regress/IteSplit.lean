import AscentTests.Setup.Blocks

/-!
# A concrete `if` splits both programs

Regression for `a14ae3e`: the split of an `if` on a `wrp` goal splits the concrete and the abstract
program on the same condition, with one fresh abstract branch per alternative.
-/

open Std.WP Lean.Order Ascent Ascent.Blocks
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Blocks.IteSplit

attribute [local ascend] wrp_bind wrp_pure

ascend_def sp (b : Bool) : BlockM (BitVec 64) Unit from
  ⦃fun _ => True⦄ (if b = true then setC 1 else setC 2) ⪯[ofStateRepr view] sp
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend []

example (b : Bool) :
    sp b = if b = true then modifyIf (fun _ => True) fun _ => 1 else modifyIf (fun _ => True) fun _ => 2 :=
  rfl

end Ascent.Blocks.IteSplit
