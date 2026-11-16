import Demo.Regs

/-!
# `zipWithAdd` with its registers lifted

`zipWithAddRegs₀` is `zipWithAddLoops` over the data memory alone, synthesized by `ascend`, and
`zipWithAddRegs` is `zipWithAddRegs₀` with its branch conditions stated as comparisons of the values. The lifting
relation `RegsRel` names the registers that become values: `rdi`, `rsi`, `rdx`, `rcx` and `rsp` are
parameters, and `rax` is the value of the loop. `zipWithAddRegs` takes the stack pointer of the entry
state `r₀ ra` for `rsp`, so the stack tests of the jumps hold and vanish. The run binds the loaded
values of `r8` as variables and keeps the guards of the instruction layer: a load and a store need a
mapped cell, and the return needs the return address of `r₀ ra` in the return slot.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def zipWithAddRegs₀ (rdi rsi rdx rcx rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rcx, rcx), (.rsp, rsp)]⦄
  (zipWithAddLoops r₀ ra) ⪯[ofStateRepr MachineData.dmem] zipWithAddRegs₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [zipWithAddLoops, wrp_forIn_lockstep_unit (R := _)]
  invariants
  · fun _ t rax => RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rcx, rcx), (.rsp, rsp),
      (.rax, rax)] t


sym_simp_def zipWithAddRegs (rdi rsi rdx rcx : BitVec 64) (rsp : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
    zipWithAddRegs₀ rdi rsi rdx rcx rsp rsp ra
  using pre [] post [stayAt_self, eq_self_iff_true, true_and, assert_true_bind, assert_true, pure_bind, bind_pure, zipWithAddRegs₀, condState_const, CondCode.cmp_nz_eq_true, CondCode.cmp_le_eq_true, BitVec.and_self,
    BitVec.toInt_zero, bind_pure_unit, pure_bind, BitVec.sub_self, BitVec.reduceSLT, Bool.not_false,
    true_and]


theorem zipWithAddRegs.refines (rdi rsi rdx rcx : BitVec 64) (rsp : BitVec 64) (ra : Int64) :
    ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rcx, rcx), (.rsp, rsp)]⦄
      (zipWithAddLoops rsp ra) ⪯[ofStateRepr MachineData.dmem] (zipWithAddRegs rdi rsi rdx rcx rsp ra)
      ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = rsp + 8, estack⟨⟩)⦄ :=
  zipWithAddRegs.eq rdi rsi rdx rcx rsp ra ▸ zipWithAddRegs₀.refines rdi rsi rdx rcx rsp rsp ra

/--
info: def Ascent.Kraken.zipWithAddRegs : BitVec 64 →
  BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rdi rsi rdx rcx rsp ra =>
  if rcx.toInt ≤ 0 then do
    StateT.assert fun m => retAddrAt m rsp = some ra
    throw ra
  else do
    let mut v := 0#64
    repeat'
      let x ← load 8 (rsi + v * 8#64)
      let x_1 ← load 8 (rdi + v * 8#64)
      store 8 (rdx + v * 8#64) (x_1 + x)
      if ¬rcx = v + 1#64 then 
        v := v + 1#64
      else
        StateT.assert fun m => retAddrAt m rsp = some ra
        throw ra
-/
#guard_msgs in
#print zipWithAddRegs

end Ascent.Kraken
