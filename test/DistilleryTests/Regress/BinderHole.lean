import DistilleryTests.Setup.Blocks

/-!
# Continuation holes applied to bound values

The decrement binds the flag to a value `z` of the abstract program; the rest of the block is a
hole applied to `z`, which the run fills by delayed assignment. The step after the decrement reads
no flag, so the continuation hole is applied to `z` and to nothing else (`demo/Demo/LiftTest`).
-/

open Std.WP Lean.Order Distillery Distillery.Blocks
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Blocks.BinderHole

attribute [local distill] wrp_bind wrp_pure

distill_def bh : BlockM (BitVec 64) Unit from
  ⦃fun _ => True⦄ (do decC; setC 3) ⪯[ofStateRepr view] bh
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill []

example : bh = (do
    let _ ← (do let z ← peek fun a => a - 1 == 0; modifyIf (fun _ => True) (· - 1); pure z)
    modifyIf (fun _ => True) fun _ => 3) := rfl

end Distillery.Blocks.BinderHole
