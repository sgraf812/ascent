import Demo.ZipF
import Demo.ArraysF

/-!
# `zipWithAdd` over arrays

`zipWithAddArr₀` is `zipWithAddF` over the output array, synthesized by `ascend`, and
`zipWithAddArr` is `zipWithAddArr₀` with the array reads in place. The input arrays are the
parameters `a` and `b`, named by their base addresses `A` and `B`. The precondition and the relation
of the loop state the layout `ArrayLayout 8 64 [(A, a), (B, b)] O n []` of `dmem`: the inputs hold
`a` and `b`, and the output array of `n` words at `O` is apart from them. Each array is apart from
the frame `Fr r₀ 0 0`, which discharges the assumption of each access that it misses the frame.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

/-- The arrays at `A`, `B` and `O` are apart from the frame `bs`. -/
def ZipApart (bs : List (BitVec 64 × Nat)) (A B O : BitVec 64) (n : Nat) : Prop :=
  Mem.Blocks.Disjoint [(A, 8 * n)] bs ∧ Mem.Blocks.Disjoint [(B, 8 * n)] bs ∧
    Mem.Blocks.Disjoint [(O, 8 * n)] bs

@[grind =] theorem zipApart_eq {bs : List (BitVec 64 × Nat)} {A B O : BitVec 64} {n : Nat} :
    ZipApart bs A B O n = (Mem.Blocks.Disjoint [(A, 8 * n)] bs ∧ Mem.Blocks.Disjoint [(B, 8 * n)] bs ∧
      Mem.Blocks.Disjoint [(O, 8 * n)] bs) := rfl

ascend_def zipWithAddArr₀ (A B O : BitVec 64) (r₀ : BitVec 64) (ra : Int64) (n : Nat) (a b : Array (BitVec 64)) :
    BlockM (Array (BitVec 64)) Unit from
  ⦃fun s => A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout 8 64 [(A, a), (B, b)] O n [] s.dmem ∧
    ZipApart (Fr r₀ 0 0) A B O n⦄
  (zipWithAddF A B O (BitVec.ofNat 64 n) r₀ ra) ⪯[ofStateRepr fun s : FState => outView 8 64 O n s.dmem]
    zipWithAddArr₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [zipWithAddF, wrp_forIn_lockstep_bind_unit
    (R := fun (v : BitVec 64) (s : FState) (i : Nat) =>
      v ≐ₙ i ∧ i < n ∧ a.size = n ∧ b.size = n ∧ ArrayLayout 8 64 [(A, a), (B, b)] O n [] s.dmem ∧
        ZipApart (Fr r₀ 0 0) A B O n)]
    with finish

sym_simp_def zipWithAddArr (ra : Int64) (n : Nat) (a b : Array (BitVec 64)) :
    BlockM (Array (BitVec 64)) Unit from zipWithAddArr₀ ra n a b
  using pre [] post [zipWithAddArr₀, BitVec.setWidth_eq, pure_bind, bind_pure_unit, condState_const, beq_eq_true_eq,
    bne_eq_true_eq]

theorem zipWithAddArr.refines (A B O : BitVec 64) (r₀ : BitVec 64) (ra : Int64) (n : Nat) (a b : Array (BitVec 64)) :
    ⦃fun s => A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout 8 64 [(A, a), (B, b)] O n [] s.dmem ∧
      ZipApart (Fr r₀ 0 0) A B O n⦄
      (zipWithAddF A B O (BitVec.ofNat 64 n) r₀ ra) ⪯[ofStateRepr fun s : FState => outView 8 64 O n s.dmem]
      (zipWithAddArr ra n a b) ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  zipWithAddArr.eq ra n a b ▸ zipWithAddArr₀.refines A B O r₀ ra n a b

end Ascent.Kraken
