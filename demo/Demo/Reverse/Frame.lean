import Demo.Reverse.Regs
import Demo.Swap.Frame

/-!
# `reverse_` with its frame split off

`reverseFrame₀` is `reverseRegs` over the split state `FState`, for the frame `Fr rsp 6 0`: the
five saved registers below the return slot and the return slot of the call to `swap`. The call
becomes `callFrame` of `swapFrame₀`, whose refinement closes the callee premise of the call rule,
and after the call the frame is as before the call. `reverseFrame` takes `rsp` for `sp`, and the
call is the body of `swapFrame₀`: the handler of the call catches the return and checks the
return address that the body threw, so only the push of the unknown return address stays.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Kraken

distill_def reverseFrame₀ [Host] [Embeds swap] (rdi rsi rax rbx r12 r14 r15 rsp sp : BitVec 64)
    (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (reverseRegs rdi rsi rax rbx r12 r14 r15 rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 6 0))] reverseFrame₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [reverseRegs, wrp_callRegs_callFrame, swapFrame₀.refines,
    wrp_forIn_lockstep_bind_unit _ _ (_, _, _, _)]
  invariants
  · fun (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) m
      (v' : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) => match v, v' with
      | (a, b, c, d), (a', b', c', d') => a ≐ a' ∧ b ≐ b' ∧ c ≐ c' ∧ d ≐ d' ∧ retAddrAt m rsp = some ra
  with finish

sym_simp_def reverseFrame [Host] [Embeds swap] (rdi rsi rax rbx r12 r14 r15 rsp : BitVec 64)
    (ra : Int64) : BlockM FState Unit from reverseFrame₀ rdi rsi rax rbx r12 r14 r15 rsp rsp ra
  using pre [] post [reverseFrame₀, swapFrame₀, callFrame, loadIn_frame, storeIn_frame, bind_assoc,
    tryCatch_bind_of_throwsOnly, ThrowsOnly.loadIn, ThrowsOnly.storeIn, BlockLoop.throw_bind,
    BlockLoop.tryCatch_throw, eq_self_iff_true, modifyIf_true_id, pure_bind, bind_pure_unit]

theorem reverseFrame.refines [Host] [FunDecls] [Embeds swap]
    (rdi rsi rax rbx r12 r14 r15 rsp : BitVec 64) (ra : Int64) :
    ⦃fun m => rsp ≐ₛ rsp ∧ retAddrAt m rsp = some ra⦄
      (reverseRegs rdi rsi rax rbx r12 r14 r15 rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 6 0))]
      (reverseFrame rdi rsi rax rbx r12 r14 r15 rsp ra)
      ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  reverseFrame.eq rdi rsi rax rbx r12 r14 r15 rsp ra ▸
    reverseFrame₀.refines rdi rsi rax rbx r12 r14 r15 rsp rsp ra

/--
info: def Distillery.Kraken.reverseFrame : BitVec 64 →
  BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM FState Unit :=
fun rdi rsi rax rbx r12 r14 r15 rsp ra =>
  condState (fun x => CondCode.c.cmp rsi 2#64) (throw ra) do
    zoom Region.frame (store 8 (rsp - 8#64) r15)
    zoom Region.frame (store 8 (rsp - 8#64 - 8#64) r14)
    zoom Region.frame (store 8 (rsp - 8#64 - 8#64 - 8#64) r12)
    zoom Region.frame (store 8 (rsp - 8#64 - 8#64 - 8#64 - 8#64) rbx)
    zoom Region.frame (store 8 (rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) rax)
    let _ ←
      { }.forIn (rdi, rdi + rsi * 8#64 + 18446744073709551608#64, rsi - 1#64, 1#64) fun x a => do
          let _ ← pushUnknownFrame (Fr rsp 6 0) (Region.frame, rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64)
          let x ← loadIn (Fr rsp 6 0) Region.dmem 8 a.fst
          let x_1 ← loadIn (Fr rsp 6 0) Region.dmem 8 a.snd.fst
          storeIn (Fr rsp 6 0) Region.dmem 8 a.fst x_1
          storeIn (Fr rsp 6 0) Region.dmem 8 a.snd.fst x
          condState (fun x => CondCode.c.cmp a.snd.snd.snd (a.snd.snd.fst - 1#64))
              (pure
                (ForInStep.yield
                  (a.fst + 8#64, a.snd.fst + 18446744073709551608#64, a.snd.snd.fst - 1#64, a.snd.snd.snd + 1#64)))
              do
              let _ ← zoom Region.frame (load 8 (rsp - 8#64 - 8#64 - 8#64 - 8#64))
              let _ ← zoom Region.frame (load 8 (rsp - 8#64 - 8#64 - 8#64))
              let _ ← zoom Region.frame (load 8 (rsp - 8#64 - 8#64))
              let _ ← zoom Region.frame (load 8 (rsp - 8#64))
              throw ra
    pure PUnit.unit
-/
#guard_msgs in
#print reverseFrame

end Distillery.Kraken
