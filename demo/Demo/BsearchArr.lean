import Demo.BsearchL
import Demo.Arrays

/-!
# The binary search over an array

`bsearchArr₀` is `bsearchL₀` over the array of `n` words at `A`, synthesized by `ascend`. The array is
the parameter `a`, and the program only reads it, so the abstract state is `Unit`. The bounds of the
search are numbers: the word `lo` holds `i` and the word `hi` holds `k`, with `i ≤ k ≤ n`. While the
loop runs, the result is `none`; the loop leaves with the optional index whose word (`IdxWord`) the
result register holds, and the program returns it.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def bsearchArr₀ (A key rax : BitVec 64) (s₀ : MachineData) (n : Nat) (a : Array (BitVec 64)) :
    BlockM Unit (Option Nat) from
  ⦃fun m => A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 m A a.size = a.toList ∧
    Mem.Mapped [(A, 8 * a.size)] m ∧ retAddrAt m (s₀.regs.get64 .rsp) = some s₀.retAddr.get!⦄
  (bsearchL₀ A (BitVec.ofNat 64 n) key rax (s₀.regs.get64 .rsp) s₀) ⪯[ofStateRepr (fun _ : DataMem => ())] bsearchArr₀
  ⦃fun v o _ => PureRefinement v o True IdxWord; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [bsearchL₀, wrp_forIn_lockstep_bind
    (fun (v : BitVec 64 × BitVec 64 × BitVec 64) m (iko : Nat × Nat × Option Nat) => match v, iko with
      | (c, d, res), (i, k, o) => c ≐ₙ i ∧ d ≐ₙ k ∧ PureRefinement res o True Unrelated ∧ i ≤ k ∧ k ≤ n ∧ a.size = n ∧
          n < 2 ^ 61 ∧ words 8 64 m A a.size = a.toList ∧ Mem.Mapped [(A, 8 * a.size)] m ∧
          retAddrAt m (s₀.regs.get64 .rsp) = some s₀.retAddr.get!)
    (fun (v : BitVec 64 × BitVec 64 × BitVec 64) _ (iko : Nat × Nat × Option Nat) => match v, iko with
      | (c, d, res), (i, k, o) => c ≐ₙ i ∧ d ≐ₙ k ∧ PureRefinement res o True IdxWord) _ (_, _, none)]
    with finish

sym_simp_def bsearchArr (key : BitVec 64) (n : Nat) (a : Array (BitVec 64)) : BlockM Unit (Option Nat) from
  bsearchArr₀ key n a
  using pre [] post [bsearchArr₀, BitVec.setWidth_eq, pure_bind, bind_pure_unit, bind_pure, condState_const,
    Nat.ble_eq, CondCode.cmp_l_eq_true, CondCode.cmp_le_eq_true]

/--
info: def Ascent.Kraken.bsearchArr : BitVec 64 → Nat → Array (BitVec 64) → BlockM Unit (Option Nat) :=
fun key n a => do
  let mut a_1 := (0, n, none)
  repeat'
    if a_1.snd.fst ≤ a_1.fst then 
      a_1 := (a_1.fst, a_1.snd.fst, none)
      break
    else
      if a[a_1.fst + (a_1.snd.fst - a_1.fst) / 2]!.toInt < key.toInt then 
        a_1 := (a_1.fst + (a_1.snd.fst - a_1.fst) / 2 + 1, a_1.snd.fst, a_1.snd.snd)
      else
        if a[a_1.fst + (a_1.snd.fst - a_1.fst) / 2]!.toInt ≤ key.toInt then 
          a_1 := (a_1.fst, a_1.snd.fst, some (a_1.fst + (a_1.snd.fst - a_1.fst) / 2))
          break
        else
          a_1 := (a_1.fst, a_1.fst + (a_1.snd.fst - a_1.fst) / 2, a_1.snd.snd)
  pure a_1.snd.snd
-/
#guard_msgs in
#print bsearchArr

theorem bsearchArr.refines (A key rax : BitVec 64) (s₀ : MachineData) (n : Nat) (a : Array (BitVec 64)) :
    ⦃fun m => A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 m A a.size = a.toList ∧
      Mem.Mapped [(A, 8 * a.size)] m ∧ retAddrAt m (s₀.regs.get64 .rsp) = some s₀.retAddr.get!⦄
      (bsearchL A (BitVec.ofNat 64 n) key rax s₀) ⪯[ofStateRepr (fun _ : DataMem => ())]
        (bsearchArr key n a)
      ⦃fun v o _ => PureRefinement v o True IdxWord; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  bsearchL.eq A (BitVec.ofNat 64 n) key rax s₀ ▸ bsearchArr.eq key n a ▸
    bsearchArr₀.refines A key rax s₀ n a

end Ascent.Kraken
