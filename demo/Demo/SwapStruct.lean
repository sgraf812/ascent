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

sym_simp_def swapT [Host] [Embeds swap] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from swapA r₀ ra
  using pre [tryCatch_bind_assoc, BlockLoop.tryCatch_pure, BlockLoop.tryCatch_throw,
    tryCatch_modifyIf_bind, tryCatch_branch_bind, tryCatch_branch, tryCatch_peek_bind,
    tryCatch_exitIf_handler, tryCatch_exitIf_cfgLoop, tryCatch_condState_bind, tryCatch_condState,
    tryCatch_map_bind, tryCatch_map_condState, tryCatch_map_throw, tryCatch_map_pure,
    tryCatch_map_modifyIf, BlockLoop.tryCatch_tryCatch, tryCatch_forIn_bind, tryCatch_map_forIn,
    tryCatch_forIn, tryCatch_forIn_bind_header, tryCatch_map_forIn_header, tryCatch_forIn_header,
    modifyIf_stay_bind_condState]
  post [swapA, swap, Program.loop, Program.entryNext, Program.firstLabel, Table.get_cons,
    Program.table, List.filterMap_cons, List.filterMap_nil, Option.map_some, Option.map_none,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Option.some.injEq,
    reduceCtorEq,
    jumpTo_none, jumpTo_some, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, cfgLoop_header, cfgLoop_eq_throw,
    ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.map, ThrowsOnly.forIn,
    ThrowsOnly.tryCatch, ThrowsOnly.modifyIf, ThrowsOnly.peek, ThrowsOnly.exitIf,
    ThrowsOnly.branch, ThrowsOnly.condState, ne_eq, not_false_eq_true, and_true, true_and,
    implies_true, forall_const, or_true, true_or, or_false, false_or, ite_true, ite_false, ite_self,
    bind_pure_unit, pure_bind, BlockLoop.throw_bind, AInstr.exitIf_bind, pure_done_eq, bind_map,
    condState_map, throw_label_step, map_exitIf, condState_exitIf_map, condState_map_exitIf,
    map_bind_exitIf, condState_bind_exitIf_map, condState_map_bind_exitIf, forIn_map_done,
    forIn_exitIf, forIn_bind_exitIf, forIn_bind_bind_exitIf, forIn_bind3_exitIf, forIn_bind4_exitIf, forIn_bind5_exitIf, forIn_bind6_exitIf, forIn_bind_exitIf_eta, forIn_throw, bind_assoc, condState_true,
    condState_false, stayIn_setReg64_rsp, BitVec.reduceSLT, Bool.not_true, eq_self_iff_true]



theorem swapT.refines [Host] [FunDecls] [Embeds swap] (r₀ : BitVec 64) (ra : Int64) :
    ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ swap ⪯[ofStateRepr abs] (swapT r₀ ra) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄ :=
  swapT.eq r₀ ra ▸ swapA.refines r₀ ra

/--
info: def Ascent.Kraken.swapT : BitVec 64 → Int64 → BlockM MachineData Unit :=
fun r₀ ra => do
  modifyIf (fun s => stayIn r₀ s = true) id
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec) (loadReg 8 Reg64.rax (fun st => st.regs.rdi.toBitVec) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rsi.toBitVec) (loadReg 8 Reg64.rcx (fun st => st.regs.rsi.toBitVec) fun w x => w)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec)
      (storeWord 8 (fun st => st.regs.rdi.toBitVec) fun st => st.regs.rcx.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rsi.toBitVec)
      (storeWord 8 (fun st => st.regs.rsi.toBitVec) fun st => st.regs.rax.toBitVec)
  exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra
-/
#guard_msgs in
#print swapT

end Ascent.Kraken
