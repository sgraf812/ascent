import Demo.L1Rel
import Demo.CfgRewrite
import Demo.LiftCall
import Demo.Swap

/-!
# `swap` as a callee

The chain of `swap` under the relation `JRel (Mem.SubSlots P)`, which hides the return slots:
`swapS` at the first layer, `swapST` structured, and `swapSL` with its registers lifted. The return of
`swapS` assumes the stack pointer of its frame and throws the label `L`, and nothing in the chain
reads the return address. The exit relation of `swapSL` states that the return restores the stack
pointer and keeps the callee-saved registers of the SysV calling convention.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRel)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken

attribute [local vcgen_simp] swap

ascend_def swapS [Host] [FunDecls] [Embeds swap] (P : DataMem) (r₀ : BitVec 64) (ra L : Int64)
    (hP : (P.loadInt r₀ 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some ra) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀⦄ swap ⪯[ofStateRel (JRel (Mem.SubSlots P))] swapS
    ⦃fun _ _ => ⊤; RetExit r₀ ra L⦄
  ascend [refines_cfg_exit (JRel (Mem.SubSlots P)) (fun _ _ h => JRel.regs h) (RetExit r₀ ra L)
    (fun _ _ _ h hs => retExit_stay h hs) (p := swap), wrp_ret_slots hP, wrp_ret_slots_cons hP] with finish


sym_simp_def swapST [Host] [Embeds swap] (r₀ : BitVec 64) (L : Int64) :
    BlockM MachineData Unit from swapS r₀ L
  using pre [tryCatch_bind_assoc, BlockLoop.tryCatch_pure, BlockLoop.tryCatch_throw,
    tryCatch_modifyIf_bind, tryCatch_branch_bind, tryCatch_branch, tryCatch_peek_bind,
    tryCatch_exitIf_handler, tryCatch_exitIf_cfgLoop, tryCatch_condState_bind, tryCatch_condState,
    tryCatch_map_bind, tryCatch_map_condState, tryCatch_map_throw, tryCatch_map_pure,
    tryCatch_map_modifyIf, BlockLoop.tryCatch_tryCatch, tryCatch_forIn_bind, tryCatch_map_forIn,
    tryCatch_forIn, tryCatch_forIn_bind_header, tryCatch_map_forIn_header, tryCatch_forIn_header,
    modifyIf_stay_bind_condState]
  post [swapS, swap, Program.loop, Program.entryNext, Program.firstLabel, Table.get_cons,
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

theorem swapST.refines [Host] [FunDecls] [Embeds swap] (P : DataMem) (r₀ : BitVec 64) (ra L : Int64)
    (hP : (P.loadInt r₀ 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some ra) :
    ⦃fun s => s.regs.get64 .rsp = r₀⦄ swap ⪯[ofStateRel (JRel (Mem.SubSlots P))] (swapST r₀ L)
      ⦃fun _ _ => ⊤; RetExit r₀ ra L⦄ :=
  swapST.eq r₀ L ▸ swapS.refines P r₀ ra L hP

/--
info: def Ascent.Kraken.swapST : BitVec 64 → Int64 → BlockM MachineData Unit :=
fun r₀ L => do
  modifyIf (fun s => stayIn r₀ s = true) id
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec) (loadReg 8 Reg64.rax (fun st => st.regs.rdi.toBitVec) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rsi.toBitVec) (loadReg 8 Reg64.rcx (fun st => st.regs.rsi.toBitVec) fun w x => w)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec)
      (storeWord 8 (fun st => st.regs.rdi.toBitVec) fun st => st.regs.rcx.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rsi.toBitVec)
      (storeWord 8 (fun st => st.regs.rsi.toBitVec) fun st => st.regs.rax.toBitVec)
  exitIf (fun s => s.regs.rsp.toBitVec = r₀) (setReg64 Reg64.rsp fun x => r₀ + 8#64) L
-/
#guard_msgs in
#print swapST

ascend_def swapSL₀ (rdi rsi rsp rbx rbp r12 r13 r14 r15 : BitVec 64) (r₀ : BitVec 64) (L : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp), (.r12, r12), (.r13, r13),
    (.r14, r14), (.r15, r15)]⦄
  (swapST r₀ L) ⪯[ofStateRepr MachineData.dmem] swapSL₀
  ⦃fun _ _ _ => False; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8#64 ∧ RegsRel [(.rbx, rbx), (.rbp, rbp),
    (.r12, r12), (.r13, r13), (.r14, r14), (.r15, r15)] t, estack⟨⟩)⦄
  ascend [swapST]
  with finish

/--
info: def Ascent.Kraken.swapSL₀ : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rdi rsi rsp r₀ L => do
  StateT.assume fun x => stayAt r₀ rsp = true
  let x ← load 8 rdi
  let x_1 ← load 8 rsi
  store 8 rdi x_1
  store 8 rsi x
  StateT.assume fun x => rsp = r₀
  throw L
-/
#guard_msgs in
#print swapSL₀

end Ascent.Kraken
