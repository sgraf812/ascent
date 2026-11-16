import Demo.Swap.Regs
import Demo.FrameCall

/-!
# `swap` with the frame of its caller split off

`swapFrame₀` is `swapRegs` over the split state `FState`, for any frame `bs`: `swap` has no frame of
its own, and its loads and stores go to `dmem`, at the abstract values `p` and `q` of the pointers
`rdi` and `rsi`. The precondition states the return address in the return slot, which lies in the
frame of the caller. `swapFrame₀.keepsFrame` states that `swap` leaves the frame unchanged, which
the call rule of a caller needs.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def swapFrame₀ (bs : List (BitVec 64 × Nat)) (rdi rsi rsp p q : BitVec 64) (ra : Int64) :
    BlockM FState Unit from
  ⦃fun m => rdi ≐ p ∧ rsi ≐ q ∧ retAddrAt m rsp = some ra ∧ Mem.Blocks.Inside rsp 8 bs⦄
  (swapRegs rdi rsi rsp ra) ⪯[ofStateRepr (FState.split bs)] swapFrame₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [swapRegs] with finish

/--
info: def Ascent.Kraken.swapFrame₀ : List (BitVec 64 × Nat) → BitVec 64 → BitVec 64 → Int64 → BlockM FState Unit :=
fun bs p q ra => do
  let x ← loadIn bs Region.dmem 8 p
  let x_1 ← loadIn bs Region.dmem 8 q
  storeIn bs Region.dmem 8 p x_1
  storeIn bs Region.dmem 8 q x
  throw ra
-/
#guard_msgs in
#print swapFrame₀

theorem swapFrame₀.keepsFrame (bs : List (BitVec 64 × Nat)) (p q : BitVec 64) (ra : Int64) :
    KeepsFrame (swapFrame₀ bs p q ra) := by
  simp (maxDischargeDepth := 8) only [swapFrame₀, KeepsFrame.bind, KeepsFrame.loadIn_dmem,
    KeepsFrame.storeIn_dmem, KeepsFrame.throw, implies_true]

grind_pattern swapFrame₀.keepsFrame => KeepsFrame (swapFrame₀ bs p q ra)

end Ascent.Kraken
