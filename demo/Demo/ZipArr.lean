import Demo.ZipL
import Demo.Arrays

/-!
# `zipWithAdd` over arrays

`zipWithAddArr` is `zipWithAddL` over the output array, synthesized by `ascend`. The input arrays
are the parameters `a` and `b`, named by their base addresses `A` and `B`. The precondition and the
relation of the loop state the layout `ArrayLayout [(A, a), (B, b)] O n [rsp]`: the inputs hold
`a` and `b`, and the output array of `n` words at `O` is apart from them and from the return slot.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken


ascend_def zipWithAddArr [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)
    (A B O rsp : BitVec 64) (n : Nat) (a b : Array (BitVec 64)) :
    BlockM (Array (BitVec 64)) Unit from
  ⦃fun m => A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout [(A, a), (B, b)] O n [rsp] m⦄
  (zipWithAddL s ra A B O (BitVec.ofNat 64 n) rsp) ⪯[ofStateRepr (outView O n)] zipWithAddArr
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_forIn_diag_bind_unit
    (I := fun m (v : BitVec 64) =>
      v.toNat < n ∧ a.size = n ∧ b.size = n ∧ ArrayLayout [(A, a), (B, b)] O n [rsp] m)]
    with finish

end Ascent.Kraken
