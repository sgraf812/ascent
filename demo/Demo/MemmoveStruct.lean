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

theorem memmove.label_ne_0_1 [Host] [Embeds memmove] : (label "LBB0_6" = label "LBB0_1") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem memmove.label_ne_0_2 [Host] [Embeds memmove] : (label "LBB0_6" = label "LBB0_3") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem memmove.label_ne_0_3 [Host] [Embeds memmove] : (label "LBB0_6" = label "LBB0_7") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem memmove.label_ne_1_0 [Host] [Embeds memmove] : (label "LBB0_1" = label "LBB0_6") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem memmove.label_ne_1_2 [Host] [Embeds memmove] : (label "LBB0_1" = label "LBB0_3") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem memmove.label_ne_1_3 [Host] [Embeds memmove] : (label "LBB0_1" = label "LBB0_7") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem memmove.label_ne_2_0 [Host] [Embeds memmove] : (label "LBB0_3" = label "LBB0_6") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem memmove.label_ne_2_1 [Host] [Embeds memmove] : (label "LBB0_3" = label "LBB0_1") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem memmove.label_ne_2_3 [Host] [Embeds memmove] : (label "LBB0_3" = label "LBB0_7") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem memmove.label_ne_3_0 [Host] [Embeds memmove] : (label "LBB0_7" = label "LBB0_6") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem memmove.label_ne_3_1 [Host] [Embeds memmove] : (label "LBB0_7" = label "LBB0_1") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem memmove.label_ne_3_2 [Host] [Embeds memmove] : (label "LBB0_7" = label "LBB0_3") = False :=
  Program.label_eq_false (p := memmove) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

sym_simp_def memmoveT [Host] [Embeds memmove] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from memmoveA r₀ ra
  using pre [tryCatch_bind_assoc, BlockLoop.tryCatch_pure, BlockLoop.tryCatch_throw,
    tryCatch_modifyIf_bind, tryCatch_branch_bind, tryCatch_branch, tryCatch_peek_bind,
    tryCatch_exitIf_handler, tryCatch_exitIf_cfgLoop, tryCatch_condState_bind, tryCatch_condState,
    tryCatch_map_bind, tryCatch_map_condState, tryCatch_map_throw, tryCatch_map_pure,
    tryCatch_map_modifyIf, BlockLoop.tryCatch_tryCatch, tryCatch_forIn_bind, tryCatch_map_forIn,
    tryCatch_forIn, tryCatch_forIn_bind_header, tryCatch_map_forIn_header, tryCatch_forIn_header,
    modifyIf_stay_bind_condState]
  post [memmoveA, memmove, Program.loop, Program.entryNext, Program.firstLabel, Table.get_cons,
    Program.table, List.filterMap_cons, List.filterMap_nil, Option.map_some, Option.map_none,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Option.some.injEq,
    reduceCtorEq, memmove.label_ne_0_1, memmove.label_ne_0_2, memmove.label_ne_0_3, memmove.label_ne_1_0, memmove.label_ne_1_2, memmove.label_ne_1_3, memmove.label_ne_2_0, memmove.label_ne_2_1, memmove.label_ne_2_3, memmove.label_ne_3_0, memmove.label_ne_3_1, memmove.label_ne_3_2,
    jumpTo_none, jumpTo_some, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, cfgLoop_header, cfgLoop_eq_throw,
    ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.map, ThrowsOnly.forIn,
    ThrowsOnly.tryCatch, ThrowsOnly.modifyIf, ThrowsOnly.peek, ThrowsOnly.exitIf,
    ThrowsOnly.branch, ThrowsOnly.condState, ne_eq, not_false_eq_true, and_true, true_and,
    implies_true, forall_const, or_true, true_or, or_false, false_or, ite_true, ite_false, ite_self,
    bind_pure_unit, pure_bind, BlockLoop.throw_bind, AInstr.exitIf_bind, pure_done_eq, bind_map,
    condState_map, throw_label_step, map_exitIf, condState_exitIf_map, condState_map_exitIf,
    map_bind_exitIf, condState_bind_exitIf_map, condState_map_bind_exitIf, forIn_map_done,
    forIn_exitIf, forIn_bind_exitIf, forIn_bind_exitIf_eta, forIn_throw, bind_assoc, condState_true,
    condState_false, stayIn_setReg64_rsp, BitVec.reduceSLT, Bool.not_true, eq_self_iff_true, BitVec.xor_self, BitVec.setWidth_zero]



theorem memmoveT.refines [Host] [FunDecls] [Embeds memmove] (r₀ : BitVec 64) (ra : Int64) :
    ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ memmove ⪯[ofStateRepr abs] (memmoveT r₀ ra) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄ :=
  memmoveT.eq r₀ ra ▸ memmoveA.refines r₀ ra

/--
info: def Ascent.Kraken.memmoveT : BitVec 64 → Int64 → BlockM MachineData Unit :=
fun r₀ ra => do
  modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.rdi.toBitVec)
  condState (fun st => CondCode.nc.cmp st.regs.rdi.toBitVec st.regs.rsi.toBitVec)
      (do
        modifyIf (fun s => stayIn r₀ s = true) id
        condState (fun st => CondCode.z.cmp (st.regs.rdx.toBitVec &&& st.regs.rdx.toBitVec) 0#64)
            (do
              modifyIf (fun s => stayIn r₀ s = true) id
              exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra)
            do
            modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.rdx.toBitVec)
            modifyIf (fun s => stayIn r₀ s = true) id
            { }.forIn PUnit.unit fun x x_1 => do
                let z ← peek fun st => st.regs.rcx.toBitVec - 1#64 == 0#64
                modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.rcx.toBitVec - 1#64)
                modifyIf (loadOk 1 (sib 1 Reg64.rsi Reg64.rdx (-1)))
                    (loadReg 1 Reg64.rdi (sib 1 Reg64.rsi Reg64.rdx (-1)) fun w x => w)
                modifyIf (storeOk 1 (sib 1 Reg64.rax Reg64.rdx (-1)))
                    (storeWord 1 (sib 1 Reg64.rax Reg64.rdx (-1)) fun st => st.regs.rdi.toBitVec)
                modifyIf (fun x => True) (setReg64 Reg64.rdx fun st => st.regs.rcx.toBitVec)
                condState (fun x => !z)
                    (do
                      modifyIf (fun s => stayIn r₀ s = true) id
                      pure (ForInStep.yield PUnit.unit))
                    do
                    modifyIf (fun s => stayIn r₀ s = true) id
                    exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra)
      (condState (fun st => CondCode.z.cmp (st.regs.rdx.toBitVec &&& st.regs.rdx.toBitVec) 0#64)
        (do
          modifyIf (fun s => stayIn r₀ s = true) id
          exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra)
        do
        modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => 0#64)
        modifyIf (fun s => stayIn r₀ s = true) id
        { }.forIn PUnit.unit fun x x_1 => do
            modifyIf (loadOk 1 (sib 1 Reg64.rsi Reg64.rcx 0))
                (loadReg 1 Reg64.rdi (sib 1 Reg64.rsi Reg64.rcx 0) fun w x => w)
            modifyIf (storeOk 1 (sib 1 Reg64.rax Reg64.rcx 0))
                (storeWord 1 (sib 1 Reg64.rax Reg64.rcx 0) fun st => st.regs.rdi.toBitVec)
            modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.rcx.toBitVec + 1#64)
            condState (fun st => CondCode.nz.cmp st.regs.rdx.toBitVec st.regs.rcx.toBitVec)
                (do
                  modifyIf (fun s => stayIn r₀ s = true) id
                  pure (ForInStep.yield PUnit.unit))
                do
                modifyIf (fun s => stayIn r₀ s = true) id
                exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra)
-/
#guard_msgs in
#print memmoveT

end Ascent.Kraken
