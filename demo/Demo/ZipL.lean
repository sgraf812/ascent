import Demo.Lift

/-!
# `zipWithAdd` with its registers lifted

`zipWithAddL₀` is `zipWithAddT` over the data memory alone, synthesized by `ascend`, and
`zipWithAddL` is `zipWithAddL₀` with its branch conditions stated as comparisons of the values. The lifting
relation `RegsRel` names the registers that become values: `rdi`, `rsi`, `rdx`, `rcx` and `rsp` are
parameters, and `rax` is the value of the loop. `zipWithAddL` takes the stack pointer of the entry
state `s₀` for `rsp`, so the stack tests of the jumps hold and vanish. The run binds the loaded
values of `r8` as variables and keeps the guards of the first layer: a load and a store need a
mapped cell, and the return needs the return address of `s₀` in the return slot.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def zipWithAddL₀ (rdi rsi rdx rcx rsp : BitVec 64) (s₀ : MachineData) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rcx, rcx), (.rsp, rsp)]⦄
  (zipWithAddT s₀) ⪯[ofStateRepr MachineData.dmem] zipWithAddL₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = s₀.regs.get64 .rsp + 8, estack⟨⟩)⦄
  ascend [zipWithAddT, wrp_forIn_lockstep_unit (R := fun t rax =>
    RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rcx, rcx), (.rsp, rsp),
      (.rax, rax)] t)]


sym_simp_def zipWithAddL (rdi rsi rdx rcx : BitVec 64) (s₀ : MachineData) :
    BlockM DataMem Unit from
    zipWithAddL₀ rdi rsi rdx rcx (s₀.regs.get64 .rsp) s₀
  using pre [] post [stayAt_self, eq_self_iff_true, true_and, assume_true_bind, assume_true, pure_bind, bind_pure, zipWithAddL₀, condState_const, CondCode.cmp_nz_eq_true, CondCode.cmp_le_eq_true, BitVec.and_self,
    BitVec.toInt_zero, bind_pure_unit, pure_bind, BitVec.sub_self, BitVec.reduceSLT, Bool.not_false,
    true_and]


theorem zipWithAddL.refines (rdi rsi rdx rcx : BitVec 64) (s₀ : MachineData) :
    ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rcx, rcx), (.rsp, s₀.regs.get64 .rsp)]⦄
      (zipWithAddT s₀) ⪯[ofStateRepr MachineData.dmem] (zipWithAddL rdi rsi rdx rcx s₀)
      ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = s₀.regs.get64 .rsp + 8, estack⟨⟩)⦄ :=
  zipWithAddL.eq rdi rsi rdx rcx s₀ ▸ zipWithAddL₀.refines rdi rsi rdx rcx (s₀.regs.get64 .rsp) s₀

/--
info: def Ascent.Kraken.zipWithAddL : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → MachineData → BlockM DataMem Unit :=
fun rdi rsi rdx rcx s₀ =>
  if rcx.toInt ≤ 0 then do
    StateT.assume fun m => retAddrAt m s₀.regs.rsp.toBitVec = some s₀.retAddr.get!
    throw s₀.retAddr.get!
  else do
    let mut v := 0#64
    repeat'
      let x ← load 8 (rsi + v * 8#64)
      let x_1 ← load 8 (rdi + v * 8#64)
      store 8 (rdx + v * 8#64) (x_1 + x)
      if ¬rcx = v + 1#64 then 
        v := v + 1#64
      else
        StateT.assume fun m => retAddrAt m s₀.regs.rsp.toBitVec = some s₀.retAddr.get!
        throw s₀.retAddr.get!
-/
#guard_msgs in
#print zipWithAddL

end Ascent.Kraken
