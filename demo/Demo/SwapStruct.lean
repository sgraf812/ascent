import Demo.CfgRewrite
import Demo.Swap

/-!
# The structured program of `swap`

`swapT` is the block loop `swapA` rewritten by the equations of `Demo.CfgRewrite`: the four steps of
`swap` followed by the return.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

namespace Ascent.Kraken

sym_simp_def swapT : BlockM MachineData Unit from swapA
  using pre [tryCatch_table_get_bind, tryCatch_bind_assoc, tryCatch_pure, BlockLoop.tryCatch_throw,
    tryCatch_modifyIf_bind, tryCatch_branch_bind, tryCatch_peek_bind, tryCatch_exitIf_bind,
    tryCatch_exitIf, tryCatch_condState_bind, tryCatch_condState, tryCatch_map_bind,
    tryCatch_map_condState, tryCatch_map_throw, tryCatch_map_exitIf, tryCatch_map_pure,
    tryCatch_map_modifyIf, BlockLoop.tryCatch_tryCatch, tryCatch_forIn_bind, tryCatch_map_forIn,
    tryCatch_forIn]
  post [swapA, swap, Table.get_cons, Program.table, List.map_cons, List.map_nil, jumpTo_none,
    jumpTo_some, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, cfgLoop_header, cfgLoop_eq_throw,
    ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.map, ThrowsOnly.forIn,
    ThrowsOnly.tryCatch, ThrowsOnly.modifyIf, ThrowsOnly.peek, ThrowsOnly.exitIf,
    ThrowsOnly.branch, ThrowsOnly.condState, ne_eq, not_false_eq_true, and_true, true_and,
    implies_true, forall_const, or_true, true_or, or_false, false_or, CfgLabel.label_eq_label,
    bind_pure_unit, pure_bind, BlockLoop.throw_bind, AInstr.exitIf_bind, pure_done_eq, bind_map,
    condState_map, throw_label_step, exitIf_step, condState_exitIf_map, condState_map_exitIf,
    condState_bind_exitIf_map, condState_map_bind_exitIf, forIn_map_done,
    forIn_exitIf, forIn_bind_exitIf, forIn_throw, bind_assoc, condState_true, condState_false,
    BitVec.xor_self, BitVec.setWidth_zero, Int64.toInt_zero, BitVec.ofInt_ofNat, BitVec.add_zero]


/--
info: def Ascent.Kraken.swapT : BlockM MachineData Unit :=
do
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec) (loadReg 8 Reg64.rax (fun st => st.regs.rdi.toBitVec) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rsi.toBitVec) (loadReg 8 Reg64.rcx (fun st => st.regs.rsi.toBitVec) fun w x => w)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec)
      (storeWord 8 (fun st => st.regs.rdi.toBitVec) fun st => st.regs.rcx.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rsi.toBitVec)
      (storeWord 8 (fun st => st.regs.rsi.toBitVec) fun st => st.regs.rax.toBitVec)
  exitIf (loadOk 8 fun st => st.regs.rsp.toBitVec) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
      CfgLabel.exit
-/
#guard_msgs in
#print swapT

theorem swapT.refines [Host] [FunDecls] [Embeds swap] (s : MachineData) (ra : Int64) :
    ⦃(· = s.push64 ra)⦄ swap ⪯[ofStateRepr abs] swapT ⦃fun _ _ => ⊤; RetRel s ra⦄ :=
  swapT.eq ▸ swapA.refines s ra

end Ascent.Kraken
