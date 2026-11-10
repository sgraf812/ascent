import Demo.BsearchL
import Demo.Arrays

/-!
# The binary search over an array

`bsearchArr₀` is `bsearchL₀` over the array of `n` words at `A`, synthesized by `ascend`. The array is
the parameter `a`, and the program only reads it, so the abstract state is `Unit`. The bounds of the
search are numbers: the word `lo` holds `i` and the word `hi` holds `k`, with `i ≤ k ≤ n`. The result
leaves through `ret`, as the word of an index or as `-1`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def bsearchArr₀ (A key rsp : BitVec 64) (n : Nat) (a : Array (BitVec 64)) : BlockM Unit Unit from
  ⦃fun m => A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 m A a.size = a.toList ∧
    Mem.Mapped [(A, 8 * a.size)] m ∧ (Mem.loadInt m rsp 8).isSome = true⦄
  (bsearchL₀ A (BitVec.ofNat 64 n) key rsp) ⪯[ofStateRepr (fun _ : DataMem => ())] bsearchArr₀
  ⦃fun _ _ _ => True;
    (fun l l' _ => ∃ v, l = .ret v ∧ ∃ j, v ≐ₙ j ∧ l' = .ret (BitVec.ofNat 64 j), estack⟨⟩)⦄
  ascend [bsearchL₀, wrp_forIn_lockstep_bind_unit
    (fun (v : BitVec 64 × BitVec 64) m (ik : Nat × Nat) => match v, ik with
      | (c, d), (i, k) => c ≐ₙ i ∧ d ≐ₙ k ∧ i ≤ k ∧ k ≤ n ∧ a.size = n ∧ n < 2 ^ 61 ∧
          words 8 64 m A a.size = a.toList ∧ Mem.Mapped [(A, 8 * a.size)] m ∧
          (Mem.loadInt m rsp 8).isSome = true) _ (_, _)]
    with finish


sym_simp_def bsearchArr (key : BitVec 64) (n : Nat) (a : Array (BitVec 64)) : BlockM Unit Unit from
  bsearchArr₀ key n a
  using pre [] post [bsearchArr₀, BitVec.setWidth_eq, pure_bind, bind_pure_unit, condState_const,
    Nat.ble_eq, CondCode.cmp_l_eq_true, CondCode.cmp_le_eq_true]

/--
info: def Ascent.Kraken.bsearchArr : BitVec 64 → Nat → Array (BitVec 64) → BlockM Unit Unit :=
fun key n a => do
  let mut a_1 := (0, n)
  repeat'
    if a_1.snd ≤ a_1.fst then 
      throw (CfgLabel.ret 18446744073709551615#64)
    else
      if a[a_1.fst + (a_1.snd - a_1.fst) / 2]!.toInt < key.toInt then 
        a_1 := (a_1.fst + (a_1.snd - a_1.fst) / 2 + 1, a_1.snd)
      else
        if a[a_1.fst + (a_1.snd - a_1.fst) / 2]!.toInt ≤ key.toInt then 
          throw (CfgLabel.ret (BitVec.ofNat 64 (a_1.fst + (a_1.snd - a_1.fst) / 2)))
        else
          a_1 := (a_1.fst, a_1.fst + (a_1.snd - a_1.fst) / 2)
-/
#guard_msgs in
#print bsearchArr

theorem bsearchArr.refines (A key rsp : BitVec 64) (n : Nat) (a : Array (BitVec 64)) :
    ⦃fun m => A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 m A a.size = a.toList ∧
      Mem.Mapped [(A, 8 * a.size)] m ∧ (Mem.loadInt m rsp 8).isSome = true⦄
      (bsearchL A (BitVec.ofNat 64 n) key rsp) ⪯[ofStateRepr (fun _ : DataMem => ())] (bsearchArr key n a)
      ⦃fun _ _ _ => True;
        (fun l l' _ => ∃ v, l = .ret v ∧ ∃ j, v ≐ₙ j ∧ l' = .ret (BitVec.ofNat 64 j), estack⟨⟩)⦄ :=
  bsearchL.eq A (BitVec.ofNat 64 n) key rsp ▸ bsearchArr.eq key n a ▸ bsearchArr₀.refines A key rsp n a

end Ascent.Kraken
