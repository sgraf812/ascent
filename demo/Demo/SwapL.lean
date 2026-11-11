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

ascend_def swapL₀ (rdi rsi rsp rbx rbp r12 r13 r14 r15 : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
    (.r14, r14), (.r15, r15)]⦄
  (swapT r₀ ra) ⪯[ofStateRepr MachineData.dmem] swapL₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8 ∧ RegsRel [(.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
    (.r14, r14), (.r15, r15)] t, estack⟨⟩)⦄
  ascend [swapT]
  with finish

sym_simp_def swapL (rdi rsi : BitVec 64) (rsp : BitVec 64) (ra : Int64) : BlockM DataMem Unit from
    swapL₀ rdi rsi rsp rsp ra
  using pre [] post [stayAt_self, eq_self_iff_true, true_and, assume_true_bind, assume_true, pure_bind, bind_pure, swapL₀, bind_pure_unit, pure_bind]


theorem swapL.refines (rdi rsi rbx rbp r12 r13 r14 r15 : BitVec 64) (rsp : BitVec 64) (ra : Int64) :
    ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
      (.r14, r14), (.r15, r15)]⦄
      (swapT rsp ra) ⪯[ofStateRepr MachineData.dmem] (swapL rdi rsi rsp ra)
      ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = rsp + 8 ∧ RegsRel [(.rbx, rbx), (.rbp, rbp), (.r12, r12),
        (.r13, r13), (.r14, r14), (.r15, r15)] t, estack⟨⟩)⦄ :=
  swapL.eq rdi rsi rsp ra ▸ swapL₀.refines rdi rsi rsp rbx rbp r12 r13 r14 r15 rsp ra

/--
info: def Ascent.Kraken.swapL : BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rdi rsi rsp ra => do
  let x ← load 8 rdi
  let x_1 ← load 8 rsi
  store 8 rdi x_1
  store 8 rsi x
  StateT.assume fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print swapL

end Ascent.Kraken
