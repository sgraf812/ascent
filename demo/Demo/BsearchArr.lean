import Demo.BsearchL
import Demo.Arrays

/-!
# The binary search over an array

`bsearchArr₀` is `bsearchL₀` over the array of `n` words at `A`, synthesized by `ascend`. The array is
the parameter `a`, and the program only reads it, so the abstract state is `Unit`. The bounds of the
search are numbers: the word `lo` holds `i` and the word `hi` holds `k`, with `i ≤ k ≤ n`. The result
register stays a word `r`, the word of an index or `-1`, and the program returns its optional index
`decodeIdx r`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def bsearchArr₀ (A key rax rsp : BitVec 64) (n : Nat) (a : Array (BitVec 64)) :
    BlockM Unit (Option Nat) from
  ⦃fun m => A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 m A a.size = a.toList ∧
    Mem.Mapped [(A, 8 * a.size)] m ∧ (Mem.loadInt m rsp 8).isSome = true⦄
  (bsearchL₀ A (BitVec.ofNat 64 n) key rax rsp) ⪯[ofStateRepr (fun _ : DataMem => ())] bsearchArr₀
  ⦃fun v o _ => PureRefinement v o True IdxWord; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [bsearchL₀, wrp_forIn_lockstep_bind
    (fun (v : BitVec 64 × BitVec 64 × BitVec 64) m (ikr : Nat × Nat × BitVec 64) => match v, ikr with
      | (c, d, res), (i, k, r) => c ≐ₙ i ∧ d ≐ₙ k ∧ res ≐ r ∧ i ≤ k ∧ k ≤ n ∧ a.size = n ∧
          n < 2 ^ 61 ∧ words 8 64 m A a.size = a.toList ∧ Mem.Mapped [(A, 8 * a.size)] m ∧
          (Mem.loadInt m rsp 8).isSome = true)
    (fun (v : BitVec 64 × BitVec 64 × BitVec 64) _ (ikr : Nat × Nat × BitVec 64) => match v, ikr with
      | (c, d, res), (i, k, r) => c ≐ₙ i ∧ d ≐ₙ k ∧ res ≐ r) _ (_, _, _)]
    with finish

sym_simp_def bsearchArr (key rax : BitVec 64) (n : Nat) (a : Array (BitVec 64)) : BlockM Unit (Option Nat) from
  bsearchArr₀ key rax n a
  using pre [] post [bsearchArr₀, BitVec.setWidth_eq, pure_bind, bind_pure_unit, bind_pure, condState_const,
    Nat.ble_eq, CondCode.cmp_l_eq_true, CondCode.cmp_le_eq_true]

/--
info: def Ascent.Kraken.bsearchArr : BitVec 64 → BitVec 64 → Nat → Array (BitVec 64) → BlockM Unit (Option Nat) :=
fun key rax n a => do
  let mut a_1 := (0, n, rax)
  repeat'
    if a_1.snd.fst ≤ a_1.fst then 
      a_1 := (a_1.fst, a_1.snd.fst, 18446744073709551615#64)
      break
    else
      if a[a_1.fst + (a_1.snd.fst - a_1.fst) / 2]!.toInt < key.toInt then 
        a_1 := (a_1.fst + (a_1.snd.fst - a_1.fst) / 2 + 1, a_1.snd.fst, a_1.snd.snd)
      else
        if a[a_1.fst + (a_1.snd.fst - a_1.fst) / 2]!.toInt ≤ key.toInt then 
          a_1 := (a_1.fst, a_1.snd.fst, BitVec.ofNat 64 (a_1.fst + (a_1.snd.fst - a_1.fst) / 2))
          break
        else
          a_1 := (a_1.fst, a_1.fst + (a_1.snd.fst - a_1.fst) / 2, a_1.snd.snd)
  pure (decodeIdx a_1.snd.snd)
-/
#guard_msgs in
#print bsearchArr

theorem bsearchArr.refines (A key rax rsp : BitVec 64) (n : Nat) (a : Array (BitVec 64)) :
    ⦃fun m => A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 m A a.size = a.toList ∧
      Mem.Mapped [(A, 8 * a.size)] m ∧ (Mem.loadInt m rsp 8).isSome = true⦄
      (bsearchL A (BitVec.ofNat 64 n) key rax rsp) ⪯[ofStateRepr (fun _ : DataMem => ())]
        (bsearchArr key rax n a)
      ⦃fun v o _ => PureRefinement v o True IdxWord; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  bsearchL.eq A (BitVec.ofNat 64 n) key rax rsp ▸ bsearchArr.eq key rax n a ▸
    bsearchArr₀.refines A key rax rsp n a

end Ascent.Kraken
