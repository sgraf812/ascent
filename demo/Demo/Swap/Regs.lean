import Demo.Regs
import Demo.Swap.Loops

/-!
# `swap` with its registers lifted

`swapRegs₀` is `swapLoops` over the data memory alone, synthesized by `distill`. `rdi`, `rsi` and `rsp` are
parameters. The callee-saved registers of the SysV calling convention, `rbx`, `rbp` and `r12` to
`r15`, are parameters too, and the exit relation states that the return leaves them unchanged.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Kraken

distill_def swapRegs₀ (rdi rsi rsp rbx rbp r12 r13 r14 r15 : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
    (.r14, r14), (.r15, r15)]⦄
  (swapLoops r₀ ra) ⪯[ofStateRepr MachineData.dmem] swapRegs₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8 ∧ RegsRel [(.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
    (.r14, r14), (.r15, r15)] t, estack⟨⟩)⦄
  distill [swapLoops]
  with finish

sym_simp_def swapRegs (rdi rsi : BitVec 64) (rsp : BitVec 64) (ra : Int64) : BlockM DataMem Unit from
    swapRegs₀ rdi rsi rsp rsp ra
  using pre [] post [stayAt_self, eq_self_iff_true, true_and, assert_true_bind, assert_true, pure_bind, bind_pure, swapRegs₀, bind_pure_unit, pure_bind]

theorem swapRegs.eq_fun (rdi rsi rsp : BitVec 64) : swapRegs₀ rdi rsi rsp rsp = swapRegs rdi rsi rsp :=
  funext (swapRegs.eq rdi rsi rsp)


theorem swapRegs.refines (rdi rsi rbx rbp r12 r13 r14 r15 : BitVec 64) (rsp : BitVec 64) (ra : Int64) :
    ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
      (.r14, r14), (.r15, r15)]⦄
      (swapLoops rsp ra) ⪯[ofStateRepr MachineData.dmem] (swapRegs rdi rsi rsp ra)
      ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = rsp + 8 ∧ RegsRel [(.rbx, rbx), (.rbp, rbp), (.r12, r12),
        (.r13, r13), (.r14, r14), (.r15, r15)] t, estack⟨⟩)⦄ :=
  swapRegs.eq rdi rsi rsp ra ▸ swapRegs₀.refines rdi rsi rsp rbx rbp r12 r13 r14 r15 rsp ra

/--
info: def Distillery.Kraken.swapRegs : BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rdi rsi rsp ra => do
  let x ← load 8 rdi
  let x_1 ← load 8 rsi
  store 8 rdi x_1
  store 8 rsi x
  StateT.assert fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print swapRegs

end Distillery.Kraken
