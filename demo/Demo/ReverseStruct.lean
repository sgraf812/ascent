import Demo.CfgRewrite
import Demo.Reverse

/-!
# The structured program of `reverse_`

`reverseT` is the block loop `reverseA` rewritten by the equations of `Demo.CfgRewrite`. The call
`withRa k` never throws, so the handlers of the block loop pass it.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRel)
open scoped Program.WP

namespace Ascent.Kraken

theorem reverse.label_ne_1 [Host] [Embeds reverse] :
    (label "_reverse_" = label "LBB1_2") = False :=
  Program.label_eq_false (p := reverse) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem reverse.label_ne_2 [Host] [Embeds reverse] :
    (label "_reverse_" = label "LBB1_4") = False :=
  Program.label_eq_false (p := reverse) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem reverse.label_ne_3 [Host] [Embeds reverse] :
    (label "LBB1_2" = label "_reverse_") = False :=
  Program.label_eq_false (p := reverse) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem reverse.label_ne_4 [Host] [Embeds reverse] :
    (label "LBB1_2" = label "LBB1_4") = False :=
  Program.label_eq_false (p := reverse) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem reverse.label_ne_5 [Host] [Embeds reverse] :
    (label "LBB1_4" = label "_reverse_") = False :=
  Program.label_eq_false (p := reverse) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem reverse.label_ne_6 [Host] [Embeds reverse] :
    (label "LBB1_4" = label "LBB1_2") = False :=
  Program.label_eq_false (p := reverse) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

sym_simp_def reverseT [Host] [Embeds reverse] (k : BitVec 64 → Int64 → BlockM MachineData Unit) (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from reverseA k r₀ ra
  using pre [tryCatch_bind_assoc, tryCatch_withRa_bind, BlockLoop.tryCatch_pure, BlockLoop.tryCatch_throw,
    tryCatch_modifyIf_bind, tryCatch_branch_bind, tryCatch_branch, tryCatch_peek_bind,
    tryCatch_exitIf_handler, tryCatch_exitIf_cfgLoop, tryCatch_condState_bind, tryCatch_condState,
    tryCatch_map_bind, tryCatch_map_condState, tryCatch_map_throw, tryCatch_map_pure,
    tryCatch_map_modifyIf, BlockLoop.tryCatch_tryCatch, tryCatch_forIn_bind, tryCatch_map_forIn,
    tryCatch_forIn, tryCatch_forIn_bind_header, tryCatch_map_forIn_header, tryCatch_forIn_header,
    modifyIf_stay_bind_condState]
  post [tryCatch_forIn_bind_header, tryCatch_map_forIn_header, tryCatch_forIn_header, reverseA, reverse, ThrowsOnly.withRa, reverse.label_ne_1, reverse.label_ne_2, reverse.label_ne_3, reverse.label_ne_4, reverse.label_ne_5, reverse.label_ne_6, Program.loop, Program.entryNext, Program.firstLabel, Table.get_cons,
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

theorem reverseT.refines [Host] [FunDecls] [Embeds reverse] (g : Fragment)
    (hg : FunDecls.at (label "_swap") = some g) (k : BitVec 64 → Int64 → BlockM MachineData Unit)
    (hk : ∀ r₀ ra, ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ g.prog
      ⪯[ofStateRel (JRel Mem.Sub)] (k r₀ ra) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄)
    (r₀ : BitVec 64) (ra : Int64) :
    ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ reverse ⪯[ofStateRel (JRel Mem.Sub)]
      (reverseT k r₀ ra) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄ :=
  reverseT.eq k r₀ ra ▸ reverseA.refines g hg k hk r₀ ra

/--
info: def Ascent.Kraken.reverseT : (BitVec 64 → Int64 → BlockM MachineData Unit) →
  BitVec 64 → Int64 → BlockM MachineData Unit :=
fun k r₀ ra => do
  modifyIf (fun s => stayIn r₀ s = true) id
  let z ← peek fun st => (st.regs.rsi.toBitVec, 2#64)
  condState (fun x => CondCode.c.cmp z.fst z.snd)
      (do
        modifyIf (fun s => stayIn r₀ s = true) id
        exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra)
      do
      modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
          (storeWord 8 (fun st => st.regs.rsp.toBitVec - 8#64) fun st => st.regs.r15.toBitVec)
      modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 8#64)
      modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
          (storeWord 8 (fun st => st.regs.rsp.toBitVec - 8#64) fun st => st.regs.r14.toBitVec)
      modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 8#64)
      modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
          (storeWord 8 (fun st => st.regs.rsp.toBitVec - 8#64) fun st => st.regs.r12.toBitVec)
      modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 8#64)
      modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
          (storeWord 8 (fun st => st.regs.rsp.toBitVec - 8#64) fun st => st.regs.rbx.toBitVec)
      modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 8#64)
      modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
          (storeWord 8 (fun st => st.regs.rsp.toBitVec - 8#64) fun st => st.regs.rax.toBitVec)
      modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 8#64)
      modifyIf (fun x => True) (setReg64 Reg64.rbx fun st => st.regs.rsi.toBitVec)
      modifyIf (fun x => True) (setReg64 Reg64.r14 fun st => st.regs.rdi.toBitVec)
      modifyIf (fun x => True) (setReg64 Reg64.r15 (sib 8 Reg64.rdi Reg64.rsi 0))
      modifyIf (fun x => True) (setReg64 Reg64.r15 fun st => st.regs.r15.toBitVec + 18446744073709551608#64)
      let _ ← peek fun st => st.regs.rbx.toBitVec - 1#64 == 0#64
      modifyIf (fun x => True) (setReg64 Reg64.rbx fun st => st.regs.rbx.toBitVec - 1#64)
      modifyIf (fun x => True) (setReg64 Reg64.r12 fun x => 1#64)
      modifyIf (fun s => stayIn r₀ s = true) id
      { }.forIn PUnit.unit fun x x_1 => do
          modifyIf (fun x => True) (setReg64 Reg64.rdi fun st => st.regs.r14.toBitVec)
          modifyIf (fun x => True) (setReg64 Reg64.rsi fun st => st.regs.r15.toBitVec)
          withRa k
          let _ ← peek fun st => st.regs.rbx.toBitVec - 1#64 == 0#64
          modifyIf (fun x => True) (setReg64 Reg64.rbx fun st => st.regs.rbx.toBitVec - 1#64)
          modifyIf (fun x => True) (setReg64 Reg64.r15 fun st => st.regs.r15.toBitVec + 18446744073709551608#64)
          modifyIf (fun x => True) (setReg64 Reg64.r14 fun st => st.regs.r14.toBitVec + 8#64)
          let z ← peek fun st => (st.regs.r12.toBitVec, st.regs.rbx.toBitVec)
          modifyIf (fun x => True) (setReg64 Reg64.r12 fun st => st.regs.r12.toBitVec + BitVec.ofInt 64 (Int64.toInt 1))
          condState (fun x => CondCode.c.cmp z.fst z.snd)
              (do
                modifyIf (fun s => stayIn r₀ s = true) id
                pure (ForInStep.yield PUnit.unit))
              do
              modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
              modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
              modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
                  (loadReg 8 Reg64.rbx (fun st => st.regs.rsp.toBitVec - 8#64) fun w x => w)
              modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
              modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
                  (loadReg 8 Reg64.r12 (fun st => st.regs.rsp.toBitVec - 8#64) fun w x => w)
              modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
              modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
                  (loadReg 8 Reg64.r14 (fun st => st.regs.rsp.toBitVec - 8#64) fun w x => w)
              modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
              modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
                  (loadReg 8 Reg64.r15 (fun st => st.regs.rsp.toBitVec - 8#64) fun w x => w)
              modifyIf (fun s => stayIn r₀ s = true) id
              exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra
-/
#guard_msgs in
#print reverseT

end Ascent.Kraken
