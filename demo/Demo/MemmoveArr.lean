import Demo.MemmoveL
import Demo.Arrays

/-!
# `memmove` over arrays

`memmoveArr₀` is `memmoveL₀` over the destination array, synthesized by `ascend`, and `memmoveArr`
is `memmoveArr₀` with the array reads in place. The source array is the parameter `a`, named by its
base address `S`; the destination of `n` bytes lies at `O`. The layout `ArrayLayout 1 8 [(S, a)] O n
[rsp]` places the source apart from the destination, so this layer keeps only the runs where the two
regions do not overlap. The test of the copy direction, whether `S ≤ O`, is the parameter `back`. Both loops carry a pair of counters: the forward loop counts up to `n`, the
backward loop counts down from `n` and reads one byte below its counter.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def memmoveArr₀ (O S : BitVec 64) (r₀ : BitVec 64) (ra : Int64) (n : Nat) (a : Array (BitVec 8)) (back : Bool) :
    BlockM (Array (BitVec 8)) Unit from
  ⦃fun m => CondCode.nc.cmp O S ≐ back ∧ S ≐ₐ a ∧ a.size = n ∧ ArrayLayout 1 8 [(S, a)] O n [(r₀, ra)] m⦄
  (memmoveL₀ O S (BitVec.ofNat 64 n) (r₀) r₀ ra) ⪯[ofStateRepr (outView 1 8 O n)] memmoveArr₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [memmoveL₀, wrp_forIn_lockstep_bind_unit _ _ (_, _)]
    invariants
    · fun (v : BitVec 64 × BitVec 64) m (ik : Nat × Nat) => match v, ik with
      | (c, d), (i, k) => c ≐ₙ i ∧ d ≐ₙ k ∧ (back = false → i < n ∧ k = n) ∧
          (back = true → 0 < i ∧ i ≤ n ∧ k = i) ∧
          a.size = n ∧ ArrayLayout 1 8 [(S, a)] O n [(r₀, ra)] m
    · fun (v : BitVec 64 × BitVec 64) m (ik : Nat × Nat) => match v, ik with
      | (c, d), (i, k) => c ≐ₙ i ∧ d ≐ₙ k ∧ (back = false → i < n ∧ k = n) ∧
          (back = true → 0 < i ∧ i ≤ n ∧ k = i) ∧
          a.size = n ∧ ArrayLayout 1 8 [(S, a)] O n [(r₀, ra)] m
    with finish

sym_simp_def memmoveArr (ra : Int64) (n : Nat) (a : Array (BitVec 8)) (back : Bool) :
    BlockM (Array (BitVec 8)) Unit from memmoveArr₀ ra n a back
  using pre [] post [memmoveArr₀, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, pure_bind,
    bind_pure_unit, condState_const, beq_eq_true_eq, bne_eq_true_eq, beq_eq_false_iff_ne, Bool.not_eq_true']

theorem memmoveArr.refines (O S : BitVec 64) (r₀ : BitVec 64) (ra : Int64) (n : Nat) (a : Array (BitVec 8)) (back : Bool) :
    ⦃fun m => CondCode.nc.cmp O S ≐ back ∧ S ≐ₐ a ∧ a.size = n ∧ ArrayLayout 1 8 [(S, a)] O n [(r₀, ra)] m⦄
      (memmoveL O S (BitVec.ofNat 64 n) r₀ ra) ⪯[ofStateRepr (outView 1 8 O n)]
      (memmoveArr ra n a back) ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  memmoveL.eq O S (BitVec.ofNat 64 n) r₀ ra ▸ memmoveArr.eq ra n a back ▸
    memmoveArr₀.refines O S r₀ ra n a back


end Ascent.Kraken
