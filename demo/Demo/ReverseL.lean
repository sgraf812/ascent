import Demo.ReverseStruct
import Demo.SwapCall

/-!
# `reverse_` with its registers lifted

`reverseL₀` is `reverseT` with `swapST` as its callee, over the data memory alone. The call becomes
`callL` of `swapSL₀`, and after the call the loop continues with the callee-saved registers `rbx`,
`r12`, `r14` and `r15` that `swap` keeps.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def reverseL₀ [Host] [Embeds swap] (rdi rsi rax rsp rbx rbp r12 r13 r14 r15 : BitVec 64) (r₀ : BitVec 64)
    (L : Int64) : BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rax, rax), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
    (.r14, r14), (.r15, r15)]⦄
  (reverseT (fun r L => swapST r L) r₀ L) ⪯[ofStateRepr MachineData.dmem] reverseL₀
  ⦃fun _ _ _ => False; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8#64, estack⟨⟩)⦄
  ascend [reverseT, wrp_callA_callL, swapSL₀.refines, wrp_forIn_lockstep_unit (R := _) (ab := (_, _, _, _))]
  invariants
  · fun _ t (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) => match v with
      | (a14, a15, b, c) => RegsRel [(.r14, a14), (.r15, a15), (.rbx, b), (.r12, c),
          (.rsp, rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64), (.rbp, rbp), (.r13, r13)] t
  with finish

sym_simp_def reverseL [Host] [Embeds swap] (rdi rsi rax rbx r12 r14 r15 rsp : BitVec 64) (L : Int64) :
    BlockM DataMem Unit from reverseL₀ rdi rsi rax rsp rbx r12 r14 r15 rsp L
  using pre [add_ofInt_neg] post [stayAt_self, eq_self_iff_true, true_and, assume_true_bind, assume_true,
    pure_bind, bind_pure, reverseL₀, bind_pure_unit, BitVec.sub_add_cancel, BitVec.ofInt_int64ToInt,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg, BitVec.ofNat_eq_ofNat, BitVec.add_neg_eq_sub]

/--
info: def Ascent.Kraken.reverseL : BitVec 64 →
  BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rdi rsi rax rbx r12 r14 r15 rsp L =>
  condState (fun x => CondCode.c.cmp rsi 2#64) (throw L) do
    store 8 (rsp - 8#64) r15
    store 8 (rsp - 8#64 - 8#64) r14
    store 8 (rsp - 8#64 - 8#64 - 8#64) r12
    store 8 (rsp - 8#64 - 8#64 - 8#64 - 8#64) rbx
    store 8 (rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) rax
    StateT.assume fun x => stayAt rsp (rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) = true
    let _ ←
      { }.forIn (rdi, rdi + rsi * 8#64 + 18446744073709551608#64, rsi - 1#64, 1#64) fun x a => do
          callL (rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64)
              (swapSL₀ a.fst a.snd.fst (rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64)
                (rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 0)
          condState (fun x => CondCode.c.cmp a.snd.snd.snd (a.snd.snd.fst - 1#64))
              (do
                StateT.assume fun x => stayAt rsp (rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) = true
                pure
                    (ForInStep.yield
                      (a.fst + 8#64, a.snd.fst + 18446744073709551608#64, a.snd.snd.fst - 1#64, a.snd.snd.snd + 1#64)))
              do
              let _ ← load 8 (rsp - 8#64 - 8#64 - 8#64 - 8#64)
              let _ ← load 8 (rsp - 8#64 - 8#64 - 8#64)
              let _ ← load 8 (rsp - 8#64 - 8#64)
              let _ ← load 8 (rsp - 8#64)
              throw L
    pure PUnit.unit
-/
#guard_msgs in
#print reverseL

end Ascent.Kraken
