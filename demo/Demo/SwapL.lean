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

ascend_def swapL₀ (rdi rsi rsp rbx rbp r12 r13 r14 r15 : BitVec 64) : BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
    (.r14, r14), (.r15, r15)]⦄
  swapT ⪯[ofStateRepr MachineData.dmem] swapL₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ RegsRel [(.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
    (.r14, r14), (.r15, r15)] t, estack⟨⟩)⦄
  ascend [swapT]
  with finish

sym_simp_def swapL (rdi rsi rsp : BitVec 64) : BlockM DataMem Unit from swapL₀ rdi rsi rsp
  using pre [] post [swapL₀, bind_pure_unit, pure_bind]

/--
info: def Ascent.Kraken.swapL : BitVec 64 → BitVec 64 → BitVec 64 → BlockM DataMem Unit :=
fun rdi rsi rsp => do
  let x ← load 8 rdi
  let x_1 ← load 8 rsi
  store 8 rsp rdi x_1
  store 8 rsp rsi x
  StateT.assume fun m => (Mem.loadInt m rsp 8).isSome = true
  throw CfgLabel.exit
-/
#guard_msgs in
#print swapL

theorem swapL.refines (rdi rsi rsp rbx rbp r12 r13 r14 r15 : BitVec 64) :
    ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
      (.r14, r14), (.r15, r15)]⦄
      swapT ⪯[ofStateRepr MachineData.dmem] (swapL rdi rsi rsp)
      ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ RegsRel [(.rbx, rbx), (.rbp, rbp), (.r12, r12),
        (.r13, r13), (.r14, r14), (.r15, r15)] t, estack⟨⟩)⦄ :=
  swapL.eq rdi rsi rsp ▸ swapL₀.refines rdi rsi rsp rbx rbp r12 r13 r14 r15

end Ascent.Kraken
