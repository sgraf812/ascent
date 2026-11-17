import Demo.Memmove.Frame
import Demo.ArraysFrame

/-!
# `memmove` over arrays

`memmoveArrays₀` is `memmoveFrame` over the destination array, synthesized by `distill`, and `memmoveArrays`
is `memmoveArrays₀` with the array reads in place. The source array is the parameter `a`, named by its
base address `S`; the destination of `n` bytes lies at `O`. The layout `ArrayLayout 1 8 [(S, a)] O n` of `dmem`
places the source apart from the destination, so this layer keeps only the runs where the two
regions do not overlap. The test of the copy direction, whether `S ≤ O`, is the parameter `back`. Both loops carry a pair of counters: the forward loop counts up to `n`, the
backward loop counts down from `n` and reads one byte below its counter.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Kraken

/-- The source array at `S` and the destination array at `O` are apart from the frame `bs`. -/
def MoveApart (bs : List (BitVec 64 × Nat)) (S O : BitVec 64) (n : Nat) : Prop :=
  Mem.Blocks.Disjoint [(S, 1 * n)] bs ∧ Mem.Blocks.Disjoint [(O, 1 * n)] bs

@[grind =] theorem moveApart_eq {bs : List (BitVec 64 × Nat)} {S O : BitVec 64} {n : Nat} :
    MoveApart bs S O n = (Mem.Blocks.Disjoint [(S, 1 * n)] bs ∧ Mem.Blocks.Disjoint [(O, 1 * n)] bs) := rfl

distill_def memmoveArrays₀ (O S : BitVec 64) (r₀ : BitVec 64) (ra : Int64) (n : Nat) (a : Array (BitVec 8)) (back : Bool) :
    BlockM (Array (BitVec 8)) Unit from
  ⦃fun s => CondCode.nc.cmp O S ≐ back ∧ S ≐ₐ a ∧ a.size = n ∧ ArrayLayout 1 8 [(S, a)] O n s.dmem ∧
    MoveApart (Fr r₀ 0 0) S O n⦄
  (memmoveFrame O S (BitVec.ofNat 64 n) r₀ ra) ⪯[ofStateRepr fun s : FState => outView 1 8 O n s.dmem] memmoveArrays₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [memmoveFrame, wrp_forIn_lockstep_bind_unit _ _ (_, _)]
    invariants
    · fun (v : BitVec 64 × BitVec 64) m (ik : Nat × Nat) => match v, ik with
      | (c, d), (i, k) => c ≐ₙ i ∧ d ≐ₙ k ∧ (back = false → i < n ∧ k = n) ∧
          (back = true → 0 < i ∧ i ≤ n ∧ k = i) ∧
          a.size = n ∧ ArrayLayout 1 8 [(S, a)] O n m.dmem ∧ MoveApart (Fr r₀ 0 0) S O n
    · fun (v : BitVec 64 × BitVec 64) m (ik : Nat × Nat) => match v, ik with
      | (c, d), (i, k) => c ≐ₙ i ∧ d ≐ₙ k ∧ (back = false → i < n ∧ k = n) ∧
          (back = true → 0 < i ∧ i ≤ n ∧ k = i) ∧
          a.size = n ∧ ArrayLayout 1 8 [(S, a)] O n m.dmem ∧ MoveApart (Fr r₀ 0 0) S O n
    with finish

sym_simp_def memmoveArrays (ra : Int64) (n : Nat) (a : Array (BitVec 8)) (back : Bool) :
    BlockM (Array (BitVec 8)) Unit from memmoveArrays₀ ra n a back
  using pre [] post [memmoveArrays₀, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, pure_bind,
    bind_pure_unit, condState_const, beq_eq_true_eq, bne_eq_true_eq, beq_eq_false_iff_ne, Bool.not_eq_true']

theorem memmoveArrays.refines (O S : BitVec 64) (r₀ : BitVec 64) (ra : Int64) (n : Nat) (a : Array (BitVec 8)) (back : Bool) :
    ⦃fun s => CondCode.nc.cmp O S ≐ back ∧ S ≐ₐ a ∧ a.size = n ∧ ArrayLayout 1 8 [(S, a)] O n s.dmem ∧
      MoveApart (Fr r₀ 0 0) S O n⦄
      (memmoveFrame O S (BitVec.ofNat 64 n) r₀ ra) ⪯[ofStateRepr fun s : FState => outView 1 8 O n s.dmem]
      (memmoveArrays ra n a back) ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  memmoveArrays.eq ra n a back ▸ memmoveArrays₀.refines O S r₀ ra n a back


end Distillery.Kraken
