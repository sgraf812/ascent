import Demo.CfgRewrite
import Demo.Bsearch
import Ascent.Refinement.Catch

/-!
# The structured program of the binary search

`bsearchT` is the block loop `bsearchA` rewritten by the equations of `Demo.CfgRewrite`: the loop
header `LBB0_3` becomes a `repeat'` loop, every other label runs its block once, and the paths
back to the header continue the loop.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

namespace Ascent.Kraken

sym_simp_def bsearchT : BlockM MachineData Unit from bsearchA
  using pre [tryCatch_table_get_bind, tryCatch_bind_assoc, tryCatch_pure, BlockLoop.tryCatch_throw,
    tryCatch_modifyIf_bind, tryCatch_branch_bind, tryCatch_peek_bind, tryCatch_exitIf_bind,
    tryCatch_exitIf, tryCatch_condState_bind, tryCatch_condState, tryCatch_map_bind,
    tryCatch_map_condState, tryCatch_map_throw, tryCatch_map_exitIf, tryCatch_map_pure,
    tryCatch_map_modifyIf, BlockLoop.tryCatch_tryCatch, tryCatch_forIn_bind, tryCatch_map_forIn,
    tryCatch_forIn]
  post [bsearchA, bsearch, Table.get_cons, Program.table, List.map_cons, List.map_nil, jumpTo_none,
    jumpTo_some, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, cfgLoop_header, cfgLoop_eq_throw,
    ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.map, ThrowsOnly.forIn,
    ThrowsOnly.tryCatch, ThrowsOnly.modifyIf, ThrowsOnly.peek, ThrowsOnly.exitIf,
    ThrowsOnly.branch, ThrowsOnly.condState, ne_eq, not_false_eq_true, and_true, true_and,
    implies_true, forall_const, or_true, true_or, or_false, false_or, CfgLabel.label_eq_label,
    bind_pure_unit, pure_bind, BlockLoop.throw_bind, AInstr.exitIf_bind, pure_done_eq, bind_map,
    condState_map, throw_label_step, map_exitIf, condState_exitIf_map, condState_map_exitIf,
    map_bind_exitIf, condState_bind_exitIf_map, condState_map_bind_exitIf, forIn_map_done,
    forIn_exitIf, forIn_bind_exitIf, forIn_bind_bind_exitIf, forIn_throw, bind_assoc, condState_true, condState_false,
    BitVec.xor_self, BitVec.setWidth_zero, modifyIf_true_bind_condState, setReg64_regs,
    Reg64s.get64_set64_eq, Reg64s.get64_set64, CondCode.z_interp_from_result, BitVec.and_self,
    BitVec.take_eq_setWidth, BitVec.setWidth_replaceLow_8]

/--
info: def Ascent.Kraken.bsearchT : BlockM MachineData Unit :=
do
  modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => 0#64)
  { }.forIn PUnit.unit fun x x_1 => do
      modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.rsi.toBitVec)
      let z ← peek fun st => CondCode.be.cmp st.regs.r8.toBitVec st.regs.rcx.toBitVec
      condState (fun x => z)
          (do
            modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec - st.regs.rcx.toBitVec)
            modifyIf (fun x => True) (setReg64 Reg64.rax fun x => 18446744073709551615#64)
            exitIf (loadOk 8 fun st => st.regs.rsp.toBitVec) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
                CfgLabel.exit)
          do
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec - st.regs.rcx.toBitVec)
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec.ushiftRight 1)
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.rcx.toBitVec + st.regs.r8.toBitVec)
          modifyIf (loadOk 8 (sib 8 Reg64.rdi Reg64.r8 0))
              (loadReg 8 Reg64.r9 (sib 8 Reg64.rdi Reg64.r8 0) fun w x => w)
          condState (fun st => CondCode.l.cmp st.regs.r9.toBitVec st.regs.rdx.toBitVec)
              (do
                modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec + 1#64)
                modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => st.regs.r9.toBitVec.replaceLow 1#8)
                modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.r8.toBitVec)
                pure (ForInStep.yield PUnit.unit))
              (condState (fun st => CondCode.le.cmp st.regs.r9.toBitVec st.regs.rdx.toBitVec)
                (do
                  modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => 0#64)
                  modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.r8.toBitVec)
                  exitIf (loadOk 8 fun st => st.regs.rsp.toBitVec)
                      (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64) CfgLabel.exit)
                do
                modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => st.regs.r9.toBitVec.replaceLow 1#8)
                modifyIf (fun x => True) (setReg64 Reg64.rsi fun st => st.regs.r8.toBitVec)
                pure (ForInStep.yield PUnit.unit))
-/
#guard_msgs in
#print bsearchT

sym_simp_def bsearchR : BlockM MachineData Unit from catchExit CfgLabel.exit bsearchT
  using pre [catchExit, tryCatch_modifyIf_bind, tryCatch_peek_bind, tryCatch_condState, tryCatch_condState_bind,
    tryCatch_bind_assoc, tryCatch_pure, tryCatch_exitIf_handle, tryCatch_forIn_return]
  post [bsearchT, eq_self, ite_true, ite_false, bind_assoc, pure_bind]

/--
info: def Ascent.Kraken.bsearchR : BlockM MachineData Unit :=
do
  modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => 0#64)
  { }.forIn PUnit.unit fun u v => do
      modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.rsi.toBitVec)
      let z ← peek fun st => CondCode.be.cmp st.regs.r8.toBitVec st.regs.rcx.toBitVec
      condState (fun x => z)
          (do
            modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec - st.regs.rcx.toBitVec)
            modifyIf (fun x => True) (setReg64 Reg64.rax fun x => 18446744073709551615#64)
            modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec)
                (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
            pure (ForInStep.done PUnit.unit))
          do
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec - st.regs.rcx.toBitVec)
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec.ushiftRight 1)
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.rcx.toBitVec + st.regs.r8.toBitVec)
          modifyIf (loadOk 8 (sib 8 Reg64.rdi Reg64.r8 0))
              (loadReg 8 Reg64.r9 (sib 8 Reg64.rdi Reg64.r8 0) fun w x => w)
          condState (fun st => CondCode.l.cmp st.regs.r9.toBitVec st.regs.rdx.toBitVec)
              (do
                modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec + 1#64)
                modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => st.regs.r9.toBitVec.replaceLow 1#8)
                modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.r8.toBitVec)
                pure (ForInStep.yield PUnit.unit))
              (condState (fun st => CondCode.le.cmp st.regs.r9.toBitVec st.regs.rdx.toBitVec)
                (do
                  modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => 0#64)
                  modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.r8.toBitVec)
                  modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec)
                      (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
                  pure (ForInStep.done PUnit.unit))
                do
                modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => st.regs.r9.toBitVec.replaceLow 1#8)
                modifyIf (fun x => True) (setReg64 Reg64.rsi fun st => st.regs.r8.toBitVec)
                pure (ForInStep.yield PUnit.unit))
-/
#guard_msgs in
#print bsearchR

theorem bsearchT.refines [Host] [FunDecls] [Embeds bsearch] (s : MachineData) (ra : Int64) :
    ⦃(· = s.push64 ra)⦄ bsearch ⪯[ofStateRepr abs] bsearchT ⦃fun _ _ => ⊤; RetRel s ra⦄ :=
  bsearchT.eq ▸ bsearchA.refines s ra

end Ascent.Kraken
