import Demo.CfgRewrite
import Demo.Memmove

/-!
# The structured program of `memmove`

`memmoveT` is the block loop `memmoveA` rewritten by the equations of `Demo.CfgRewrite`: the entry
test on `rdi` and `rsi` is a `condState` whose branches hold the two copy loops, each a `repeat'`
loop that continues on its jump to itself and leaves by the return.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

namespace Ascent.Kraken

sym_simp_def memmoveT : BlockM MachineData Unit from memmoveA
  using pre [tryCatch_table_get_bind, tryCatch_bind_assoc, tryCatch_pure, BlockLoop.tryCatch_throw,
    tryCatch_modifyIf_bind, tryCatch_branch_bind, tryCatch_peek_bind, tryCatch_exitIf_bind, tryCatch_exitIf,
    tryCatch_condState_bind, tryCatch_condState, cfgLoop_eq_tryCatch]
  post [memmoveA, memmove, Table.get_cons, Program.table, List.map_cons, List.map_nil,
    jumpTo_none, jumpTo_some, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, cfgLoop_eq_tryCatch, cfgLoop_header,
    cfgLoop_eq_throw, ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.map, ThrowsOnly.forIn,
    ThrowsOnly.modifyIf, ThrowsOnly.peek, ThrowsOnly.exitIf, ThrowsOnly.condState, ne_eq,
    not_false_eq_true, and_true, true_and, implies_true, forall_const, CfgLabel.label_eq_label,
    bind_pure_unit, pure_bind, BlockLoop.throw_bind, AInstr.exitIf_bind, forIn_map_done, forIn_exitIf,
    bind_assoc, condState_true, condState_false, BitVec.xor_self,
    BitVec.setWidth_zero]

/--
info: def Ascent.Kraken.memmoveT : BlockM MachineData Unit :=
do
  modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.rdi.toBitVec)
  condState (fun st => CondCode.nc.cmp st.regs.rdi.toBitVec st.regs.rsi.toBitVec)
      (condState (fun st => CondCode.z.cmp (st.regs.rdx.toBitVec &&& st.regs.rdx.toBitVec) 0#64)
        (exitIf (loadOk 8 fun st => st.regs.rsp.toBitVec) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
          CfgLabel.exit)
        do
        modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.rdx.toBitVec)
        { }.forIn PUnit.unit fun x x_1 => do
            let z ← peek fun st => st.regs.rcx.toBitVec - 1#64 == 0#64
            modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.rcx.toBitVec - 1#64)
            modifyIf (loadOk 1 (sib 1 Reg64.rsi Reg64.rdx (-1)))
                (loadReg 1 Reg64.rdi (sib 1 Reg64.rsi Reg64.rdx (-1)) fun w x => w)
            modifyIf (storeOk 1 (sib 1 Reg64.rax Reg64.rdx (-1)))
                (storeWord 1 (sib 1 Reg64.rax Reg64.rdx (-1)) fun st => st.regs.rdi.toBitVec)
            modifyIf (fun x => True) (setReg64 Reg64.rdx fun st => st.regs.rcx.toBitVec)
            condState (fun x => !z) (pure (ForInStep.yield PUnit.unit))
                (exitIf (loadOk 8 fun st => st.regs.rsp.toBitVec)
                  (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64) CfgLabel.exit))
      (condState (fun st => CondCode.z.cmp (st.regs.rdx.toBitVec &&& st.regs.rdx.toBitVec) 0#64)
        (exitIf (loadOk 8 fun st => st.regs.rsp.toBitVec) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
          CfgLabel.exit)
        do
        modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => 0#64)
        { }.forIn PUnit.unit fun x x_1 => do
            modifyIf (loadOk 1 (sib 1 Reg64.rsi Reg64.rcx 0))
                (loadReg 1 Reg64.rdi (sib 1 Reg64.rsi Reg64.rcx 0) fun w x => w)
            modifyIf (storeOk 1 (sib 1 Reg64.rax Reg64.rcx 0))
                (storeWord 1 (sib 1 Reg64.rax Reg64.rcx 0) fun st => st.regs.rdi.toBitVec)
            modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.rcx.toBitVec + 1#64)
            condState (fun st => CondCode.nz.cmp st.regs.rdx.toBitVec st.regs.rcx.toBitVec)
                (pure (ForInStep.yield PUnit.unit))
                (exitIf (loadOk 8 fun st => st.regs.rsp.toBitVec)
                  (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64) CfgLabel.exit))
-/
#guard_msgs in
#print memmoveT

theorem memmoveT.refines [Host] [FunDecls] [Embeds memmove] (s : MachineData) (ra : Int64) :
    ⦃(· = s.push64 ra)⦄ memmove ⪯[ofStateRepr abs] memmoveT ⦃fun _ _ => ⊤; RetRel s ra⦄ :=
  memmoveT.eq ▸ memmoveA.refines s ra

end Ascent.Kraken
