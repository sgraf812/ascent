import Demo.ZipL
import Demo.Arrays

/-!
# `zipWithAdd` over arrays

`zipWithAddArr₀` is `zipWithAddL` over the output array, synthesized by `ascend`, and
`zipWithAddArr` is `zipWithAddArr₀` with the array reads in place. The input arrays
are the parameters `a` and `b`, named by their base addresses `A` and `B`. The precondition and the
relation of the loop state the layout `ArrayLayout 8 64 [(A, a), (B, b)] O n [rsp]`: the inputs hold
`a` and `b`, and the output array of `n` words at `O` is apart from them and from the return slot.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken


ascend_def zipWithAddArr₀ (A B O rsp : BitVec 64) (n : Nat) (a b : Array (BitVec 64)) :
    BlockM (Array (BitVec 64)) Unit from
  ⦃fun m => A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout 8 64 [(A, a), (B, b)] O n [rsp] m⦄
  (zipWithAddL₀ A B O (BitVec.ofNat 64 n) rsp) ⪯[ofStateRepr (outView 8 64 O n)] zipWithAddArr₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [zipWithAddL₀, wrp_forIn_lockstep_bind_unit
    (R := fun (v : BitVec 64) m (i : Nat) =>
      v ≐ₙ i ∧ i < n ∧ a.size = n ∧ b.size = n ∧ ArrayLayout 8 64 [(A, a), (B, b)] O n [rsp] m)]
    with finish

sym_simp_def zipWithAddArr (n : Nat) (a b : Array (BitVec 64)) : BlockM (Array (BitVec 64)) Unit from
  zipWithAddArr₀ n a b
  using pre [] post [zipWithAddArr₀, BitVec.setWidth_eq, pure_bind, bind_pure_unit, condState_const, beq_eq_true_eq,
    bne_eq_true_eq]

theorem zipWithAddArr.refines (A B O rsp : BitVec 64) (n : Nat) (a b : Array (BitVec 64)) :
    ⦃fun m => A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout 8 64 [(A, a), (B, b)] O n [rsp] m⦄
      (zipWithAddL A B O (BitVec.ofNat 64 n) rsp) ⪯[ofStateRepr (outView 8 64 O n)]
      (zipWithAddArr n a b) ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  zipWithAddL.eq A B O (BitVec.ofNat 64 n) rsp ▸ zipWithAddArr.eq n a b ▸
    zipWithAddArr₀.refines A B O rsp n a b

end Ascent.Kraken
