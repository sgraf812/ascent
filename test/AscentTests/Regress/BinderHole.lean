import AscentTests.Setup.Blocks

/-!
# Continuation holes applied to bound values

The decrement binds the flag to a value `z` of the abstract program; the rest of the block is a
hole applied to `z`, which the run fills by delayed assignment. The step after the decrement reads
no flag, so the continuation hole is applied to `z` and to nothing else (`demo/Demo/LiftTest`).
-/

open Std.WP Lean.Order Ascent Ascent.Blocks
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Blocks.BinderHole

attribute [local ascend] wrp_bind wrp_pure

ascend_def bh : BlockM (BitVec 64) Unit from
  ⦃fun _ => True⦄ (do decC; setC 3) ⪯[ofStateRepr view] bh
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend []

example : bh = (do
    let _ ← (do let z ← peek fun a => a - 1 == 0; modifyIf (fun _ => True) (· - 1); pure z)
    modifyIf (fun _ => True) fun _ => 3) := rfl

end Ascent.Blocks.BinderHole
