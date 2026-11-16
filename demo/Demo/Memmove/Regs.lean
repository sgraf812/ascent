import Demo.Regs
import Demo.Memmove.Loops

/-!
# `memmove` with its registers lifted

`memmoveRegs₀` is `memmoveLoops` over the data memory alone, synthesized by `ascend`. The lifting relation
`RegsRel` names the registers that become values: `rdi`, `rsi`, `rdx` and `rsp` are parameters, and
both loops carry `rcx` and `rdx` as their value. `rax` holds `dst` from the first instruction on, and
the exit relation states that it still does at the return.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def memmoveRegs₀ (rdi rsi rdx rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) : BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rsp, rsp)]⦄
  (memmoveLoops r₀ ra) ⪯[ofStateRepr MachineData.dmem] memmoveRegs₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rax = rdi ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [memmoveLoops, wrp_forIn_lockstep_unit (R := _) (ab := (_, _))]
  invariants
  · fun _ t (v : BitVec 64 × BitVec 64) => match v with
    | (rcx, rdx) => RegsRel [(.rsi, rsi), (.rax, rdi), (.rsp, rsp), (.rcx, rcx), (.rdx, rdx)] t
  · fun _ t (v : BitVec 64 × BitVec 64) => match v with
    | (rcx, rdx) => RegsRel [(.rsi, rsi), (.rax, rdi), (.rsp, rsp), (.rcx, rcx), (.rdx, rdx)] t
  with finish

sym_simp_def memmoveRegs (rdi rsi rdx : BitVec 64) (rsp : BitVec 64) (ra : Int64) : BlockM DataMem Unit from
    memmoveRegs₀ rdi rsi rdx rsp rsp ra
  using pre [] post [stayAt_self, eq_self_iff_true, true_and, assert_true_bind, assert_true, pure_bind, bind_pure, memmoveRegs₀, condState_const, CondCode.cmp_nz_eq_true, CondCode.cmp_z_eq_true,
    CondCode.cmp_nc_eq_true, BitVec.and_self, BitVec.mul_one, bind_pure_unit, pure_bind, Bool.not_eq_true',
    beq_eq_true_eq, beq_eq_false_iff_ne, add_ofInt_neg_one]



theorem memmoveRegs.refines (rdi rsi rdx : BitVec 64) (rsp : BitVec 64) (ra : Int64) :
    ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rsp, rsp)]⦄
      (memmoveLoops rsp ra) ⪯[ofStateRepr MachineData.dmem] (memmoveRegs rdi rsi rdx rsp ra)
      ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rax = rdi ∧ t.regs.get64 .rsp = rsp + 8, estack⟨⟩)⦄ :=
  memmoveRegs.eq rdi rsi rdx rsp ra ▸ memmoveRegs₀.refines rdi rsi rdx rsp rsp ra

/--
info: def Ascent.Kraken.memmoveRegs : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rdi rsi rdx rsp ra =>
  if rsi ≤ rdi then
    if rdx = 0#64 then do
      StateT.assert fun m => retAddrAt m rsp = some ra
      throw ra
    else do
      let mut a := (rdx, rdx)
      repeat'
        let x ← load 1 (rsi + a.snd - 1#64)
        store 1 (rdi + a.snd - 1#64) x
        if ¬a.fst - 1#64 = 0#64 then 
          a := (a.fst - 1#64, a.fst - 1#64)
        else
          StateT.assert fun m => retAddrAt m rsp = some ra
          throw ra
  else
    if rdx = 0#64 then do
      StateT.assert fun m => retAddrAt m rsp = some ra
      throw ra
    else do
      let mut a := (0#64, rdx)
      repeat'
        let x ← load 1 (rsi + a.fst)
        store 1 (rdi + a.fst) x
        if ¬a.snd = a.fst + 1#64 then 
          a := (a.fst + 1#64, a.snd)
        else
          StateT.assert fun m => retAddrAt m rsp = some ra
          throw ra
-/
#guard_msgs in
#print memmoveRegs

end Ascent.Kraken
