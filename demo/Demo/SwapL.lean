import Demo.Lift
import Demo.SwapStruct

/-!
# `swap` with its registers lifted

`swapL₀` is `swapT` over the data memory alone, synthesized by `ascend`. `rdi`, `rsi` and `rsp` are
parameters. The callee-saved registers of the SysV calling convention, `rbx`, `rbp` and `r12` to
`r15`, are parameters too, and the exit relation states that the return leaves them unchanged.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def swapL₀ (rdi rsi rsp rbx rbp r12 r13 r14 r15 : BitVec 64) (s₀ : MachineData) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
    (.r14, r14), (.r15, r15)]⦄
  (swapT s₀) ⪯[ofStateRepr MachineData.dmem] swapL₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = s₀.regs.get64 .rsp + 8 ∧ RegsRel [(.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
    (.r14, r14), (.r15, r15)] t, estack⟨⟩)⦄
  ascend [swapT]
  with finish

sym_simp_def swapL (rdi rsi rsp : BitVec 64) (s₀ : MachineData) : BlockM DataMem Unit from
    swapL₀ rdi rsi rsp s₀
  using pre [] post [swapL₀, bind_pure_unit, pure_bind]


theorem swapL.refines (rdi rsi rsp rbx rbp r12 r13 r14 r15 : BitVec 64) (s₀ : MachineData) :
    ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
      (.r14, r14), (.r15, r15)]⦄
      (swapT s₀) ⪯[ofStateRepr MachineData.dmem] (swapL rdi rsi rsp s₀)
      ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = s₀.regs.get64 .rsp + 8 ∧ RegsRel [(.rbx, rbx), (.rbp, rbp), (.r12, r12),
        (.r13, r13), (.r14, r14), (.r15, r15)] t, estack⟨⟩)⦄ :=
  swapL.eq rdi rsi rsp s₀ ▸ swapL₀.refines rdi rsi rsp rbx rbp r12 r13 r14 r15 s₀

/--
info: def Ascent.Kraken.swapL : BitVec 64 → BitVec 64 → BitVec 64 → MachineData → BlockM DataMem Unit :=
fun rdi rsi rsp s₀ => do
  StateT.assume fun x => stayAt s₀.regs.rsp.toBitVec rsp = true
  let x ← load 8 rdi
  let x_1 ← load 8 rsi
  store 8 rsp rdi x_1
  store 8 rsp rsi x
  StateT.assume fun m => rsp = s₀.regs.rsp.toBitVec ∧ retAddrAt m rsp = some s₀.retAddr.get!
  throw s₀.retAddr.get!
-/
#guard_msgs in
#print swapL

end Ascent.Kraken
