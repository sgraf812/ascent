import AscentTests.Setup.Blocks

/-!
# A value carried across steps, in a table of cells

Regression for `efc5cac`. The first cell decrements `r`, branches on the flag that the decrement
wrote, and continues after the branch. The abstract cell binds the flag to a value `z`, and the
continuation after the branch is a hole under `z`. The cells share one abstract table, so the next
cell's goal meets that hole; the hole keeps the context of the cell it fills.
-/

open Std.WP Lean.Order Ascent Ascent.Blocks
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Blocks.HoleScope

attribute [local ascend] wrp_bind wrp_pure

noncomputable def c1 : BlockM CS Unit := do decC; jnzC 1; setC 5
noncomputable def c2 : BlockM CS Unit := setC 7

ascend_def hs : BlockM (BitVec 64) Unit from
  ⦃fun _ => True⦄ (cells [(1, c1), (2, c2)]) ⪯[ofStateRepr view] hs
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_cells (I := fun _ => True), c1, c2] with finish

/--
info: def Ascent.Blocks.HoleScope.hs : BlockM (BitVec 64) Unit :=
cellsAt
  [((1, c1).fst, do
      let x ←
        do
          let z ← peek fun a => a - 1 == 0
          modifyIf (fun x => True) fun x => x - 1
          pure z
      branch (fun x_1 => !x) (Lbl.lbl 1)
      modifyIf (fun x => True) fun x => 5),
    ((2, c2).fst, modifyIf (fun x => True) fun x => 7)]
  (List.map Prod.fst [(1, c1), (2, c2)])
-/
#guard_msgs in
#print hs

end Ascent.Blocks.HoleScope
