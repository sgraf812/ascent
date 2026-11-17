import DistilleryTests.Setup.Blocks

/-!
# A concrete `if` splits both programs

Regression for `a14ae3e`: the split of an `if` on a `wrp` goal splits the concrete and the abstract
program on the same condition, with one fresh abstract branch per alternative.
-/

open Std.WP Lean.Order Distillery Distillery.Blocks
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Blocks.IteSplit

attribute [local distill] wrp_bind wrp_pure

distill_def sp (b : Bool) : BlockM (BitVec 64) Unit from
  ⦃fun _ => True⦄ (if b = true then setC 1 else setC 2) ⪯[ofStateRepr view] sp
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill []

example (b : Bool) :
    sp b = if b = true then modifyIf (fun _ => True) fun _ => 1 else modifyIf (fun _ => True) fun _ => 2 :=
  rfl

end Distillery.Blocks.IteSplit
