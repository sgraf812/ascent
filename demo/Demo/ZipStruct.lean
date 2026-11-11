import Demo.CfgRewrite
import Demo.Zip

/-!
# The structured program of `zipWithAdd`

`zipWithAddT` is the block loop `zipWithAddA` rewritten by the equations of `Demo.CfgRewrite`: the
entry test is a `condState`, the loop block a `repeat'` loop that continues on its jump to itself
and leaves it by the return. `zipWithAddT.refines` is the refinement of `zipWithAddA`,
rewritten along `zipWithAddT.eq`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

namespace Ascent.Kraken

theorem zipWithAdd.label_ne [Host] [Embeds zipWithAdd] :
    (label "LBB0_2" = label "LBB0_3") = False :=
  Program.label_eq_false (p := zipWithAdd) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem zipWithAdd.label_ne' [Host] [Embeds zipWithAdd] :
    (label "LBB0_3" = label "LBB0_2") = False :=
  Program.label_eq_false (p := zipWithAdd) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

sym_simp_def zipWithAddT [Host] [Embeds zipWithAdd] (s₀ : MachineData) :
    BlockM MachineData Unit from zipWithAddA s₀
  using pre [tryCatch_bind_assoc, BlockLoop.tryCatch_pure, BlockLoop.tryCatch_throw,
    tryCatch_modifyIf_bind, tryCatch_branch_bind, tryCatch_branch, tryCatch_peek_bind, tryCatch_exitIf_handler,
    tryCatch_exitIf_cfgLoop, tryCatch_condState_bind, tryCatch_condState, tryCatch_map_bind,
    tryCatch_map_condState, tryCatch_map_throw, tryCatch_map_pure, tryCatch_map_modifyIf,
    BlockLoop.tryCatch_tryCatch, tryCatch_forIn_bind, tryCatch_map_forIn, tryCatch_forIn,
    modifyIf_stay_bind_condState]
  post [zipWithAddA, zipWithAdd, Program.loop, Program.entryNext, Program.firstLabel, Table.get_cons,
    Program.table, List.filterMap_cons, List.filterMap_nil, Option.map_some, Option.map_none,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Option.some.injEq,
    reduceCtorEq, zipWithAdd.label_ne, zipWithAdd.label_ne',
    jumpTo_none, jumpTo_some, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, cfgLoop_header, cfgLoop_eq_throw,
    ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.map, ThrowsOnly.forIn,
    ThrowsOnly.tryCatch, ThrowsOnly.modifyIf, ThrowsOnly.peek, ThrowsOnly.exitIf,
    ThrowsOnly.branch, ThrowsOnly.condState, ne_eq, not_false_eq_true, and_true, true_and,
    implies_true, forall_const, or_true, true_or, or_false, false_or, ite_true, ite_false, ite_self,
    bind_pure_unit, pure_bind, BlockLoop.throw_bind, AInstr.exitIf_bind, pure_done_eq, bind_map,
    condState_map, throw_label_step, map_exitIf, condState_exitIf_map, condState_map_exitIf,
    map_bind_exitIf, condState_bind_exitIf_map, condState_map_bind_exitIf, forIn_map_done,
    forIn_exitIf, forIn_bind_exitIf, forIn_bind_exitIf_eta, forIn_throw, bind_assoc, condState_true, condState_false,
    stayIn_setReg64_rsp, BitVec.reduceSLT, Bool.not_true,
    BitVec.xor_self, BitVec.setWidth_zero]

theorem zipWithAddT.refines [Host] [FunDecls] [Embeds zipWithAdd] (s₀ : MachineData) :
    ⦃(· = s₀)⦄ zipWithAdd ⪯[ofStateRepr abs] (zipWithAddT s₀) ⦃fun _ _ => ⊤; AddrRel s₀⦄ :=
  zipWithAddT.eq s₀ ▸ zipWithAddA.refines s₀

/--
info: def Ascent.Kraken.zipWithAddT : MachineData → BlockM MachineData Unit :=
fun s₀ =>
  condState (fun st => CondCode.le.cmp (st.regs.rcx.toBitVec &&& st.regs.rcx.toBitVec) 0#64)
    (do
      modifyIf (fun s => stayIn s₀.regs.rsp.toBitVec s = true) id
      exitIf (retOk s₀) (setReg64 Reg64.rsp fun x => s₀.regs.rsp.toBitVec + 8#64) s₀.retAddr.get!)
    do
    modifyIf (fun x => True) (setReg64 Reg64.rax fun st => 0#64)
    modifyIf (fun s => stayIn s₀.regs.rsp.toBitVec s = true) id
    { }.forIn PUnit.unit fun x x_1 => do
        modifyIf (loadOk 8 (sib 8 Reg64.rsi Reg64.rax 0))
            (loadReg 8 Reg64.r8 (sib 8 Reg64.rsi Reg64.rax 0) fun w x => w)
        modifyIf (loadOk 8 (sib 8 Reg64.rdi Reg64.rax 0))
            (loadReg 8 Reg64.r8 (sib 8 Reg64.rdi Reg64.rax 0) fun w st => w + st.regs.r8.toBitVec)
        modifyIf (storeOk 8 (sib 8 Reg64.rdx Reg64.rax 0))
            (storeWord 8 (sib 8 Reg64.rdx Reg64.rax 0) fun st => st.regs.r8.toBitVec)
        modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.rax.toBitVec + 1#64)
        condState (fun st => CondCode.nz.cmp st.regs.rcx.toBitVec st.regs.rax.toBitVec)
            (do
              modifyIf (fun s => stayIn s₀.regs.rsp.toBitVec s = true) id
              pure (ForInStep.yield PUnit.unit))
            do
            modifyIf (fun s => stayIn s₀.regs.rsp.toBitVec s = true) id
            exitIf (retOk s₀) (setReg64 Reg64.rsp fun x => s₀.regs.rsp.toBitVec + 8#64) s₀.retAddr.get!
-/
#guard_msgs in
#print zipWithAddT

end Ascent.Kraken
