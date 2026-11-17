import Demo.Bsearch.Frame
import Demo.ArraysFrame

/-!
# The binary search over an array

`bsearchArrays₀` is `bsearchFrame` over the array of `n` words at `A`, synthesized by `distill`. The array is
the parameter `a`, and the program only reads it, so the abstract state is `Unit`. The bounds of the
search are numbers: the word `lo` holds `i` and the word `hi` holds `k`, with `i ≤ k ≤ n`. While the
loop runs, the result is `none`; the loop leaves with the optional index whose word (`IdxWord`) the
result register holds, and the program returns it.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Kraken

distill_def bsearchArrays₀ (A key rax : BitVec 64) (r₀ : BitVec 64) (n : Nat) (a : Array (BitVec 64)) :
    BlockM Unit (Option Nat) from
  ⦃fun s => A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 s.dmem A a.size = a.toList ∧
    Mem.Mapped [(A, 8 * a.size)] s.dmem ∧ Mem.Blocks.Disjoint [(A, 8 * a.size)] (Fr r₀ 0 0)⦄
  (bsearchFrame A (BitVec.ofNat 64 n) key rax r₀) ⪯[ofStateRepr (fun _ : FState => ())] bsearchArrays₀
  ⦃fun v o _ => PureRefinement v o True IdxWord; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [bsearchFrame, wrp_forIn_lockstep_bind _ _ _ (_, _, none)]
    invariants
    · fun (v : BitVec 64 × BitVec 64 × BitVec 64) m (iko : Nat × Nat × Option Nat) => match v, iko with
      | (c, d, res), (i, k, o) => c ≐ₙ i ∧ d ≐ₙ k ∧ PureRefinement res o True Unrelated ∧ i ≤ k ∧ k ≤ n ∧ a.size = n ∧
          n < 2 ^ 61 ∧ words 8 64 m.dmem A a.size = a.toList ∧ Mem.Mapped [(A, 8 * a.size)] m.dmem ∧
          Mem.Blocks.Disjoint [(A, 8 * a.size)] (Fr r₀ 0 0)
    · fun (v : BitVec 64 × BitVec 64 × BitVec 64) _ (iko : Nat × Nat × Option Nat) => match v, iko with
      | (c, d, res), (i, k, o) => c ≐ₙ i ∧ d ≐ₙ k ∧ PureRefinement res o True IdxWord
    with finish

sym_simp_def bsearchArrays (key : BitVec 64) (n : Nat) (a : Array (BitVec 64)) : BlockM Unit (Option Nat) from
  bsearchArrays₀ key n a
  using pre [] post [bsearchArrays₀, BitVec.setWidth_eq, pure_bind, bind_pure_unit, bind_pure, condState_const,
    Nat.ble_eq, CondCode.cmp_l_eq_true, CondCode.cmp_le_eq_true]

/--
info: def Distillery.Kraken.bsearchArrays : BitVec 64 → Nat → Array (BitVec 64) → BlockM Unit (Option Nat) :=
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
#print bsearchArrays

theorem bsearchArrays.refines (A key rax : BitVec 64) (r₀ : BitVec 64) (n : Nat) (a : Array (BitVec 64)) :
    ⦃fun s => A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 s.dmem A a.size = a.toList ∧
      Mem.Mapped [(A, 8 * a.size)] s.dmem ∧ Mem.Blocks.Disjoint [(A, 8 * a.size)] (Fr r₀ 0 0)⦄
      (bsearchFrame A (BitVec.ofNat 64 n) key rax r₀) ⪯[ofStateRepr (fun _ : FState => ())]
        (bsearchArrays key n a)
      ⦃fun v o _ => PureRefinement v o True IdxWord; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  bsearchArrays.eq key n a ▸ bsearchArrays₀.refines A key rax r₀ n a

end Distillery.Kraken
