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

theorem bsearch.label_ne_0_1 [Host] [Embeds bsearch] : (label "LBB0_1" = label "LBB0_2") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_0_2 [Host] [Embeds bsearch] : (label "LBB0_1" = label "LBB0_3") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_0_3 [Host] [Embeds bsearch] : (label "LBB0_1" = label "LBB0_7") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_0_4 [Host] [Embeds bsearch] : (label "LBB0_1" = label "LBB0_8") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_0_5 [Host] [Embeds bsearch] : (label "LBB0_1" = label "LBB0_9") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_1_0 [Host] [Embeds bsearch] : (label "LBB0_2" = label "LBB0_1") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_1_2 [Host] [Embeds bsearch] : (label "LBB0_2" = label "LBB0_3") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_1_3 [Host] [Embeds bsearch] : (label "LBB0_2" = label "LBB0_7") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_1_4 [Host] [Embeds bsearch] : (label "LBB0_2" = label "LBB0_8") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_1_5 [Host] [Embeds bsearch] : (label "LBB0_2" = label "LBB0_9") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_2_0 [Host] [Embeds bsearch] : (label "LBB0_3" = label "LBB0_1") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_2_1 [Host] [Embeds bsearch] : (label "LBB0_3" = label "LBB0_2") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_2_3 [Host] [Embeds bsearch] : (label "LBB0_3" = label "LBB0_7") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_2_4 [Host] [Embeds bsearch] : (label "LBB0_3" = label "LBB0_8") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_2_5 [Host] [Embeds bsearch] : (label "LBB0_3" = label "LBB0_9") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_3_0 [Host] [Embeds bsearch] : (label "LBB0_7" = label "LBB0_1") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_3_1 [Host] [Embeds bsearch] : (label "LBB0_7" = label "LBB0_2") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_3_2 [Host] [Embeds bsearch] : (label "LBB0_7" = label "LBB0_3") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_3_4 [Host] [Embeds bsearch] : (label "LBB0_7" = label "LBB0_8") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_3_5 [Host] [Embeds bsearch] : (label "LBB0_7" = label "LBB0_9") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_4_0 [Host] [Embeds bsearch] : (label "LBB0_8" = label "LBB0_1") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_4_1 [Host] [Embeds bsearch] : (label "LBB0_8" = label "LBB0_2") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_4_2 [Host] [Embeds bsearch] : (label "LBB0_8" = label "LBB0_3") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_4_3 [Host] [Embeds bsearch] : (label "LBB0_8" = label "LBB0_7") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_4_5 [Host] [Embeds bsearch] : (label "LBB0_8" = label "LBB0_9") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_5_0 [Host] [Embeds bsearch] : (label "LBB0_9" = label "LBB0_1") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_5_1 [Host] [Embeds bsearch] : (label "LBB0_9" = label "LBB0_2") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_5_2 [Host] [Embeds bsearch] : (label "LBB0_9" = label "LBB0_3") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_5_3 [Host] [Embeds bsearch] : (label "LBB0_9" = label "LBB0_7") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem bsearch.label_ne_5_4 [Host] [Embeds bsearch] : (label "LBB0_9" = label "LBB0_8") = False :=
  Program.label_eq_false (p := bsearch) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

sym_simp_def bsearchT [Host] [Embeds bsearch] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from bsearchA r₀ ra
  using pre [tryCatch_bind_assoc, BlockLoop.tryCatch_pure, BlockLoop.tryCatch_throw,
    tryCatch_modifyIf_bind, tryCatch_branch_bind, tryCatch_branch, tryCatch_peek_bind,
    tryCatch_exitIf_handler, tryCatch_exitIf_cfgLoop, tryCatch_condState_bind, tryCatch_condState,
    tryCatch_map_bind, tryCatch_map_condState, tryCatch_map_throw, tryCatch_map_pure,
    tryCatch_map_modifyIf, BlockLoop.tryCatch_tryCatch, tryCatch_forIn_bind, tryCatch_map_forIn,
    tryCatch_forIn, tryCatch_forIn_bind_header, tryCatch_map_forIn_header, tryCatch_forIn_header,
    modifyIf_stay_bind_condState]
  post [bsearchA, bsearch, Program.loop, Program.entryNext, Program.firstLabel, Table.get_cons,
    Program.table, List.filterMap_cons, List.filterMap_nil, Option.map_some, Option.map_none,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Option.some.injEq,
    reduceCtorEq, bsearch.label_ne_0_1, bsearch.label_ne_0_2, bsearch.label_ne_0_3, bsearch.label_ne_0_4, bsearch.label_ne_0_5, bsearch.label_ne_1_0, bsearch.label_ne_1_2, bsearch.label_ne_1_3, bsearch.label_ne_1_4, bsearch.label_ne_1_5, bsearch.label_ne_2_0, bsearch.label_ne_2_1, bsearch.label_ne_2_3, bsearch.label_ne_2_4, bsearch.label_ne_2_5, bsearch.label_ne_3_0, bsearch.label_ne_3_1, bsearch.label_ne_3_2, bsearch.label_ne_3_4, bsearch.label_ne_3_5, bsearch.label_ne_4_0, bsearch.label_ne_4_1, bsearch.label_ne_4_2, bsearch.label_ne_4_3, bsearch.label_ne_4_5, bsearch.label_ne_5_0, bsearch.label_ne_5_1, bsearch.label_ne_5_2, bsearch.label_ne_5_3, bsearch.label_ne_5_4,
    jumpTo_none, jumpTo_some, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, cfgLoop_header, cfgLoop_eq_throw,
    ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.map, ThrowsOnly.forIn,
    ThrowsOnly.tryCatch, ThrowsOnly.modifyIf, ThrowsOnly.peek, ThrowsOnly.exitIf,
    ThrowsOnly.branch, ThrowsOnly.condState, ne_eq, not_false_eq_true, and_true, true_and,
    implies_true, forall_const, or_true, true_or, or_false, false_or, ite_true, ite_false, ite_self,
    bind_pure_unit, pure_bind, BlockLoop.throw_bind, AInstr.exitIf_bind, pure_done_eq, bind_map,
    condState_map, throw_label_step, map_exitIf, condState_exitIf_map, condState_map_exitIf,
    map_bind_exitIf, condState_bind_exitIf_map, condState_map_bind_exitIf, forIn_map_done,
    forIn_exitIf, forIn_bind_exitIf, forIn_bind_bind_exitIf, forIn_bind_exitIf_eta, forIn_throw, bind_assoc, condState_true,
    condState_false, stayIn_setReg64_rsp, BitVec.reduceSLT, Bool.not_true, eq_self_iff_true, BitVec.xor_self, BitVec.setWidth_zero]

sym_simp_def bsearchR [Host] [Embeds bsearch] (r₀ : BitVec 64) (ra : Int64) : BlockM MachineData Unit from
    catchExit ra (bsearchT r₀ ra)
  using pre [catchExit, tryCatch_modifyIf_bind, tryCatch_peek_bind, tryCatch_condState, tryCatch_condState_bind,
    tryCatch_bind_assoc, BlockLoop.tryCatch_pure, tryCatch_exitIf_handle, tryCatch_forIn_return,
    tryCatch_ite]
  post [bsearchT, eq_self, ite_true, ite_false, bind_assoc, pure_bind, modifyIf_true_bind_condState,
    modifyIf_id_bind_condState, AInstr.setReg64_regs, Reg64s.get64_set64_eq, Reg64s.get64_set64,
    CondCode.z_interp_from_result, BitVec.and_self, BitVec.take_eq_setWidth, BitVec.setWidth_replaceLow_8,
    condState_true, condState_false, id_eq]



theorem bsearchT.refines [Host] [FunDecls] [Embeds bsearch] (r₀ : BitVec 64) (ra : Int64) :
    ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ bsearch ⪯[ofStateRepr abs] (bsearchT r₀ ra) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄ :=
  bsearchT.eq r₀ ra ▸ bsearchA.refines r₀ ra

/--
info: def Ascent.Kraken.bsearchT : BitVec 64 → Int64 → BlockM MachineData Unit :=
fun r₀ ra => do
  modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => 0#64)
  modifyIf (fun s => stayIn r₀ s = true) id
  { }.forIn PUnit.unit fun x x_1 => do
      modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.rsi.toBitVec)
      let z ← peek fun st => CondCode.be.cmp st.regs.r8.toBitVec st.regs.rcx.toBitVec
      modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec - st.regs.rcx.toBitVec)
      condState (fun x => z)
          (do
            modifyIf (fun s => stayIn r₀ s = true) id
            modifyIf (fun x => True) (setReg64 Reg64.rax fun x => 18446744073709551615#64)
            modifyIf (fun s => stayIn r₀ s = true) id
            exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra)
          do
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec.ushiftRight 1)
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.rcx.toBitVec + st.regs.r8.toBitVec)
          modifyIf (loadOk 8 (sib 8 Reg64.rdi Reg64.r8 0))
              (loadReg 8 Reg64.r9 (sib 8 Reg64.rdi Reg64.r8 0) fun w x => w)
          condState (fun st => CondCode.l.cmp st.regs.r9.toBitVec st.regs.rdx.toBitVec)
              (do
                modifyIf (fun s => stayIn r₀ s = true) id
                modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec + 1#64)
                modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => st.regs.r9.toBitVec.replaceLow 1#8)
                modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.r8.toBitVec)
                modifyIf (fun s => stayIn r₀ s = true) id
                condState
                    (fun st =>
                      CondCode.z.interp
                        (StatusFlags.from_result (st.regs.r9.toBitVec.take 8 &&& st.regs.r9.toBitVec.take 8)
                          { cf := false, af := false, of := false }))
                    (do
                      modifyIf (fun s => stayIn r₀ s = true) id
                      exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra)
                    do
                    modifyIf (fun s => stayIn r₀ s = true) id
                    pure (ForInStep.yield PUnit.unit))
              (condState (fun st => CondCode.le.cmp st.regs.r9.toBitVec st.regs.rdx.toBitVec)
                (do
                  modifyIf (fun s => stayIn r₀ s = true) id
                  modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => 0#64)
                  modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.r8.toBitVec)
                  modifyIf (fun s => stayIn r₀ s = true) id
                  condState
                      (fun st =>
                        CondCode.z.interp
                          (StatusFlags.from_result (st.regs.r9.toBitVec.take 8 &&& st.regs.r9.toBitVec.take 8)
                            { cf := false, af := false, of := false }))
                      (do
                        modifyIf (fun s => stayIn r₀ s = true) id
                        exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra)
                      do
                      modifyIf (fun s => stayIn r₀ s = true) id
                      pure (ForInStep.yield PUnit.unit))
                do
                modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => st.regs.r9.toBitVec.replaceLow 1#8)
                modifyIf (fun x => True) (setReg64 Reg64.rsi fun st => st.regs.r8.toBitVec)
                modifyIf (fun s => stayIn r₀ s = true) id
                condState
                    (fun st =>
                      CondCode.z.interp
                        (StatusFlags.from_result (st.regs.r9.toBitVec.take 8 &&& st.regs.r9.toBitVec.take 8)
                          { cf := false, af := false, of := false }))
                    (do
                      modifyIf (fun s => stayIn r₀ s = true) id
                      exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra)
                    do
                    modifyIf (fun s => stayIn r₀ s = true) id
                    pure (ForInStep.yield PUnit.unit))
-/
#guard_msgs in
#print bsearchT

/--
info: def Ascent.Kraken.bsearchR : BitVec 64 → Int64 → BlockM MachineData Unit :=
fun r₀ ra => do
  modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => 0#64)
  modifyIf (fun s => stayIn r₀ s = true) id
  { }.forIn PUnit.unit fun u v => do
      modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.rsi.toBitVec)
      let z ← peek fun st => CondCode.be.cmp st.regs.r8.toBitVec st.regs.rcx.toBitVec
      condState (fun x => z)
          (do
            modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec - st.regs.rcx.toBitVec)
            modifyIf (fun s => stayIn r₀ s = true) id
            modifyIf (fun x => True) (setReg64 Reg64.rax fun x => 18446744073709551615#64)
            modifyIf (fun s => stayIn r₀ s = true) id
            modifyIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64)
            pure (ForInStep.done PUnit.unit))
          do
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec - st.regs.rcx.toBitVec)
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec.ushiftRight 1)
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.rcx.toBitVec + st.regs.r8.toBitVec)
          modifyIf (loadOk 8 (sib 8 Reg64.rdi Reg64.r8 0))
              (loadReg 8 Reg64.r9 (sib 8 Reg64.rdi Reg64.r8 0) fun w x => w)
          condState (fun st => CondCode.l.cmp st.regs.r9.toBitVec st.regs.rdx.toBitVec)
              (do
                modifyIf (fun s => stayIn r₀ s = true) id
                modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.r8.toBitVec + 1#64)
                modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => st.regs.r9.toBitVec.replaceLow 1#8)
                modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.r8.toBitVec)
                modifyIf (fun s => stayIn r₀ s = true) id
                modifyIf (fun s => stayIn r₀ s = true) id
                pure (ForInStep.yield PUnit.unit))
              (condState (fun st => CondCode.le.cmp st.regs.r9.toBitVec st.regs.rdx.toBitVec)
                (do
                  modifyIf (fun s => stayIn r₀ s = true) id
                  modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => 0#64)
                  modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.r8.toBitVec)
                  modifyIf (fun s => stayIn r₀ s = true) id
                  modifyIf (fun s => stayIn r₀ s = true) id
                  modifyIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64)
                  pure (ForInStep.done PUnit.unit))
                do
                modifyIf (fun x => True) (setReg64 Reg64.r9 fun st => st.regs.r9.toBitVec.replaceLow 1#8)
                modifyIf (fun x => True) (setReg64 Reg64.rsi fun st => st.regs.r8.toBitVec)
                modifyIf (fun s => stayIn r₀ s = true) id
                modifyIf (fun s => stayIn r₀ s = true) id
                pure (ForInStep.yield PUnit.unit))
-/
#guard_msgs in
#print bsearchR

end Ascent.Kraken
