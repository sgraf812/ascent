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


ascend_def zipWithAddArr₀ (A B O : BitVec 64) (s₀ : MachineData) (n : Nat) (a b : Array (BitVec 64)) :
    BlockM (Array (BitVec 64)) Unit from
  ⦃fun m => A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout 8 64 [(A, a), (B, b)] O n [(s₀.regs.get64 .rsp, s₀.retAddr.get!)] m⦄
  (zipWithAddL₀ A B O (BitVec.ofNat 64 n) (s₀.regs.get64 .rsp) s₀) ⪯[ofStateRepr (outView 8 64 O n)] zipWithAddArr₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [zipWithAddL₀, wrp_forIn_lockstep_bind_unit
    (R := fun (v : BitVec 64) m (i : Nat) =>
      v ≐ₙ i ∧ i < n ∧ a.size = n ∧ b.size = n ∧
        ArrayLayout 8 64 [(A, a), (B, b)] O n [(s₀.regs.get64 .rsp, s₀.retAddr.get!)] m)]
    with finish



sym_simp_def zipWithAddArr (s₀ : MachineData) (n : Nat) (a b : Array (BitVec 64)) :
    BlockM (Array (BitVec 64)) Unit from zipWithAddArr₀ s₀ n a b
  using pre [] post [zipWithAddArr₀, BitVec.setWidth_eq, pure_bind, bind_pure_unit, condState_const, beq_eq_true_eq,
    bne_eq_true_eq]

theorem zipWithAddArr.refines (A B O : BitVec 64) (s₀ : MachineData) (n : Nat) (a b : Array (BitVec 64)) :
    ⦃fun m => A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout 8 64 [(A, a), (B, b)] O n [(s₀.regs.get64 .rsp, s₀.retAddr.get!)] m⦄
      (zipWithAddL A B O (BitVec.ofNat 64 n) s₀) ⪯[ofStateRepr (outView 8 64 O n)]
      (zipWithAddArr s₀ n a b) ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  zipWithAddL.eq A B O (BitVec.ofNat 64 n) s₀ ▸ zipWithAddArr.eq s₀ n a b ▸
    zipWithAddArr₀.refines A B O s₀ n a b


end Ascent.Kraken

