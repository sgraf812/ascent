import Demo.CfgRewrite
import Distillery.Tactic.VCGen.Command

/-!
# Stack frames

Regression tests for the instruction-layer synthesis (`distill_def`) and the structuring (`sym_simp_def`) of leaf
functions that move `rsp` or access the stack. Every program text in this file is hand-written x64 in
AT&T syntax, not compiler output. The `#print` of each structured definition records the current
result.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

namespace Distillery.Kraken.Tests.StackFrame

/-! ## Word pushes and pops of callee-saved registers

The text saves `rbx` and `r12`, overwrites both, and restores them in reverse order, so `rsp` is at
the entry value `r₀` before `ret`. -/

/-
  pushq %rbx
  pushq %r12
  movq %rdi, %rbx
  movq %rsi, %r12
  movq %rbx, %rax
  popq %r12
  popq %rbx
  retq
-/
def pushPop : Program := [
  .instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low .rbx .W64))))),
  .instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low .r12 .W64))))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rbx .W64)) (.regOrMem (.reg (.low .rdi .W64))))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .r12 .W64)) (.regOrMem (.reg (.low .rsi .W64))))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64))))),
  .instr (.regular .W64 .W64 (.pop (.reg (.low .r12 .W64)))),
  .instr (.regular .W64 .W64 (.pop (.reg (.low .rbx .W64)))),
  .instr (.regular .W64 .W64 .ret)]

attribute [local vcgen_simp] pushPop

distill_def pushPopInstr [Host] [FunDecls] [Embeds pushPop] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ pushPop ⪯[ofStateRepr abs] pushPopInstr ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  distill [refines_cfg (p := pushPop) (habs := abs_regs)] with finish

sym_simp_def pushPopLoops [Host] [Embeds pushPop] (r₀ : BitVec 64) (ra : Int64) : BlockM MachineData Unit from pushPopInstr r₀ ra
  using pre [] post [pushPopInstr, pushPop, Program.loop, Program.entryNext, Program.firstLabel_nil, Program.firstLabel_cons, Program.table,
    Program.blocks_eq, List.filterMap_cons, List.filterMap_nil, List.reverse_nil, Table.get_cons,
    Option.some.injEq, reduceCtorEq, jumpTo_none, cfgLoop_eq_throw, Table.get?_nil, tryCatch_bind_assoc,
    tryCatch_modifyIf_bind, tryCatch_exitIf_cfgLoop, stayIn_setReg64_rsp, BitVec.reduceSLT, Bool.not_true,
    eq_self_iff_true, implies_true, bind_assoc, AInstr.exitIf_bind, bind_pure_unit, pure_bind]

/--
info: def Distillery.Kraken.Tests.StackFrame.pushPopLoops : BitVec 64 → Int64 → BlockM MachineData Unit :=
fun r₀ ra => do
  modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
      (storeWord 8 (fun st => st.regs.rsp.toBitVec - 8#64) fun st => st.regs.rbx.toBitVec)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 8#64)
  modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
      (storeWord 8 (fun st => st.regs.rsp.toBitVec - 8#64) fun st => st.regs.r12.toBitVec)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 8#64)
  modifyIf (fun x => True) (setReg64 Reg64.rbx fun st => st.regs.rdi.toBitVec)
  modifyIf (fun x => True) (setReg64 Reg64.r12 fun st => st.regs.rsi.toBitVec)
  modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.rbx.toBitVec)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
  modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
      (loadReg 8 Reg64.r12 (fun st => st.regs.rsp.toBitVec - 8#64) fun w x => w)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
  modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
      (loadReg 8 Reg64.rbx (fun st => st.regs.rsp.toBitVec - 8#64) fun w x => w)
  exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra
-/
#guard_msgs in
#print pushPopLoops

/-! ## A local area

`subq $16, %rsp` reserves two words. The text spills `rdi` and `rsi` at `8(%rsp)` and `(%rsp)`, reloads
them, and releases the area with `addq $16, %rsp`. -/

/-
  subq $16, %rsp
  movq %rdi, 8(%rsp)
  movq %rsi, (%rsp)
  movq 8(%rsp), %rax
  movq (%rsp), %rcx
  addq $16, %rsp
  retq
-/
def locals : Program := [
  .instr (.regular .W64 .W64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 16)))),
  .instr (.regular .W64 .W64 (.mov (.mem ⟨some (.reg .rsp), none, .int64 8⟩) (.regOrMem (.reg (.low .rdi .W64))))),
  .instr (.regular .W64 .W64 (.mov (.mem ⟨some (.reg .rsp), none, .int64 0⟩) (.regOrMem (.reg (.low .rsi .W64))))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.regOrMem (.mem ⟨some (.reg .rsp), none, .int64 8⟩)))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rcx .W64)) (.regOrMem (.mem ⟨some (.reg .rsp), none, .int64 0⟩)))),
  .instr (.regular .W64 .W64 (.add (.reg (.low .rsp .W64)) (.imm (.int64 16)))),
  .instr (.regular .W64 .W64 .ret)]

attribute [local vcgen_simp] locals

distill_def localsInstr [Host] [FunDecls] [Embeds locals] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ locals ⪯[ofStateRepr abs] localsInstr ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  distill [refines_cfg (p := locals) (habs := abs_regs)] with finish

sym_simp_def localsLoops [Host] [Embeds locals] (r₀ : BitVec 64) (ra : Int64) : BlockM MachineData Unit from localsInstr r₀ ra
  using pre [] post [localsInstr, locals, Program.loop, Program.entryNext, Program.firstLabel_nil, Program.firstLabel_cons, Program.table,
    Program.blocks_eq, List.filterMap_cons, List.filterMap_nil, List.reverse_nil, Table.get_cons,
    Option.some.injEq, reduceCtorEq, jumpTo_none, cfgLoop_eq_throw, Table.get?_nil, tryCatch_bind_assoc,
    tryCatch_modifyIf_bind, tryCatch_exitIf_cfgLoop, stayIn_setReg64_rsp, BitVec.reduceSLT, Bool.not_true,
    eq_self_iff_true, implies_true, bind_assoc, AInstr.exitIf_bind, bind_pure_unit, pure_bind]

/--
info: def Distillery.Kraken.Tests.StackFrame.localsLoops : BitVec 64 → Int64 → BlockM MachineData Unit :=
fun r₀ ra => do
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 16#64)
  modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 8))
      (storeWord 8 (fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 8)) fun st => st.regs.rdi.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec)
      (storeWord 8 (fun st => st.regs.rsp.toBitVec) fun st => st.regs.rsi.toBitVec)
  modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 8))
      (loadReg 8 Reg64.rax (fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 8)) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec) (loadReg 8 Reg64.rcx (fun st => st.regs.rsp.toBitVec) fun w x => w)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 16#64)
  exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra
-/
#guard_msgs in
#print localsLoops

/-! ## Byte spills at an unaligned offset

The text stores the low byte of `rax` at `3(%rsp)` in a local area, reloads it into the low byte of
`rcx`, and reloads it zero-extended into `edx`. -/

/-
  subq $16, %rsp
  movb %al, 3(%rsp)
  movb 3(%rsp), %cl
  movzbl 3(%rsp), %edx
  addq $16, %rsp
  retq
-/
def bytes : Program := [
  .instr (.regular .W64 .W64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 16)))),
  .instr (.regular .W64 .W8 (.mov (.mem ⟨some (.reg .rsp), none, .int64 3⟩) (.regOrMem (.reg (.low .rax .W8))))),
  .instr (.regular .W64 .W8 (.mov (.reg (.low .rcx .W8)) (.regOrMem (.mem ⟨some (.reg .rsp), none, .int64 3⟩)))),
  .instr (.regular .W64 .W32 (.movzx (w' := .W8) (.reg (.low .rdx .W32)) (.mem ⟨some (.reg .rsp), none, .int64 3⟩))),
  .instr (.regular .W64 .W64 (.add (.reg (.low .rsp .W64)) (.imm (.int64 16)))),
  .instr (.regular .W64 .W64 .ret)]

attribute [local vcgen_simp] bytes

distill_def bytesInstr [Host] [FunDecls] [Embeds bytes] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ bytes ⪯[ofStateRepr abs] bytesInstr ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  distill [refines_cfg (p := bytes) (habs := abs_regs)] with finish

sym_simp_def bytesLoops [Host] [Embeds bytes] (r₀ : BitVec 64) (ra : Int64) : BlockM MachineData Unit from bytesInstr r₀ ra
  using pre [] post [bytesInstr, bytes, Program.loop, Program.entryNext, Program.firstLabel_nil, Program.firstLabel_cons, Program.table,
    Program.blocks_eq, List.filterMap_cons, List.filterMap_nil, List.reverse_nil, Table.get_cons,
    Option.some.injEq, reduceCtorEq, jumpTo_none, cfgLoop_eq_throw, Table.get?_nil, tryCatch_bind_assoc,
    tryCatch_modifyIf_bind, tryCatch_exitIf_cfgLoop, stayIn_setReg64_rsp, BitVec.reduceSLT, Bool.not_true,
    eq_self_iff_true, implies_true, bind_assoc, AInstr.exitIf_bind, bind_pure_unit, pure_bind]

/--
info: def Distillery.Kraken.Tests.StackFrame.bytesLoops : BitVec 64 → Int64 → BlockM MachineData Unit :=
fun r₀ ra => do
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 16#64)
  modifyIf (storeOk 1 fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 3))
      (storeWord 1 (fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 3)) fun st => st.regs.rax.toBitVec)
  modifyIf (loadOk 1 fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 3))
      (loadReg 1 Reg64.rcx (fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 3)) fun w st =>
        st.regs.rcx.toBitVec.replaceLow (BitVec.setWidth 8 w))
  modifyIf (loadOk 1 fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 3))
      (loadReg 1 Reg64.rdx (fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 3)) fun w x => w)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 16#64)
  exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra
-/
#guard_msgs in
#print bytesLoops

/-! ## 16-bit pushes, pops and spills

`pushw %ax` and `popw %cx` move `rsp` by two. The text then stores the low 16 bits of `rax` at the odd
offset `5(%rsp)` and reloads them into the low 16 bits of `rdx`. -/

/-
  subq $8, %rsp
  pushw %ax
  popw %cx
  movw %ax, 5(%rsp)
  movw 5(%rsp), %dx
  addq $8, %rsp
  retq
-/
def halves : Program := [
  .instr (.regular .W64 .W64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 8)))),
  .instr (.regular .W64 .W16 (.push (.regOrMem (.reg (.low .rax .W16))))),
  .instr (.regular .W64 .W16 (.pop (.reg (.low .rcx .W16)))),
  .instr (.regular .W64 .W16 (.mov (.mem ⟨some (.reg .rsp), none, .int64 5⟩) (.regOrMem (.reg (.low .rax .W16))))),
  .instr (.regular .W64 .W16 (.mov (.reg (.low .rdx .W16)) (.regOrMem (.mem ⟨some (.reg .rsp), none, .int64 5⟩)))),
  .instr (.regular .W64 .W64 (.add (.reg (.low .rsp .W64)) (.imm (.int64 8)))),
  .instr (.regular .W64 .W64 .ret)]

attribute [local vcgen_simp] halves

distill_def halvesInstr [Host] [FunDecls] [Embeds halves] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ halves ⪯[ofStateRepr abs] halvesInstr ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  distill [refines_cfg (p := halves) (habs := abs_regs)] with finish

sym_simp_def halvesLoops [Host] [Embeds halves] (r₀ : BitVec 64) (ra : Int64) : BlockM MachineData Unit from halvesInstr r₀ ra
  using pre [] post [halvesInstr, halves, Program.loop, Program.entryNext, Program.firstLabel_nil, Program.firstLabel_cons, Program.table,
    Program.blocks_eq, List.filterMap_cons, List.filterMap_nil, List.reverse_nil, Table.get_cons,
    Option.some.injEq, reduceCtorEq, jumpTo_none, cfgLoop_eq_throw, Table.get?_nil, tryCatch_bind_assoc,
    tryCatch_modifyIf_bind, tryCatch_exitIf_cfgLoop, stayIn_setReg64_rsp, BitVec.reduceSLT, Bool.not_true,
    eq_self_iff_true, implies_true, bind_assoc, AInstr.exitIf_bind, bind_pure_unit, pure_bind]

/--
info: def Distillery.Kraken.Tests.StackFrame.halvesLoops : BitVec 64 → Int64 → BlockM MachineData Unit :=
fun r₀ ra => do
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 8#64)
  modifyIf (storeOk 2 fun st => st.regs.rsp.toBitVec - 2#64)
      (storeWord 2 (fun st => st.regs.rsp.toBitVec - 2#64) fun st => st.regs.rax.toBitVec)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 2#64)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 2#64)
  modifyIf (loadOk 2 fun st => st.regs.rsp.toBitVec - 2#64)
      (loadReg 2 Reg64.rcx (fun st => st.regs.rsp.toBitVec - 2#64) fun w st =>
        st.regs.rcx.toBitVec.replaceLow (BitVec.setWidth 16 w))
  modifyIf (storeOk 2 fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 5))
      (storeWord 2 (fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 5)) fun st => st.regs.rax.toBitVec)
  modifyIf (loadOk 2 fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 5))
      (loadReg 2 Reg64.rdx (fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 5)) fun w st =>
        st.regs.rdx.toBitVec.replaceLow (BitVec.setWidth 16 w))
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
  exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra
-/
#guard_msgs in
#print halvesLoops

/-! ## A red-zone leaf

The text stores and loads a word at `-8(%rsp)` and a byte at `-11(%rsp)`, below `rsp`, and keeps `rsp` at its
entry value. -/

/-
  movq %rdi, -8(%rsp)
  movb %al, -11(%rsp)
  movq -8(%rsp), %rax
  movzbl -11(%rsp), %ecx
  retq
-/
def redZone : Program := [
  .instr (.regular .W64 .W64 (.mov (.mem ⟨some (.reg .rsp), none, .int64 (-8)⟩) (.regOrMem (.reg (.low .rdi .W64))))),
  .instr (.regular .W64 .W8 (.mov (.mem ⟨some (.reg .rsp), none, .int64 (-11)⟩) (.regOrMem (.reg (.low .rax .W8))))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.regOrMem (.mem ⟨some (.reg .rsp), none, .int64 (-8)⟩)))),
  .instr (.regular .W64 .W32 (.movzx (w' := .W8) (.reg (.low .rcx .W32)) (.mem ⟨some (.reg .rsp), none, .int64 (-11)⟩))),
  .instr (.regular .W64 .W64 .ret)]

attribute [local vcgen_simp] redZone

distill_def redZoneInstr [Host] [FunDecls] [Embeds redZone] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ redZone ⪯[ofStateRepr abs] redZoneInstr ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  distill [refines_cfg (p := redZone) (habs := abs_regs)] with finish

sym_simp_def redZoneLoops [Host] [Embeds redZone] (r₀ : BitVec 64) (ra : Int64) : BlockM MachineData Unit from redZoneInstr r₀ ra
  using pre [] post [redZoneInstr, redZone, Program.loop, Program.entryNext, Program.firstLabel_nil, Program.firstLabel_cons, Program.table,
    Program.blocks_eq, List.filterMap_cons, List.filterMap_nil, List.reverse_nil, Table.get_cons,
    Option.some.injEq, reduceCtorEq, jumpTo_none, cfgLoop_eq_throw, Table.get?_nil, tryCatch_bind_assoc,
    tryCatch_modifyIf_bind, tryCatch_exitIf_cfgLoop, stayIn_setReg64_rsp, BitVec.reduceSLT, Bool.not_true,
    eq_self_iff_true, implies_true, bind_assoc, AInstr.exitIf_bind, bind_pure_unit, pure_bind]

/--
info: def Distillery.Kraken.Tests.StackFrame.redZoneLoops : BitVec 64 → Int64 → BlockM MachineData Unit :=
fun r₀ ra => do
  modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (-8).toInt)
      (storeWord 8 (fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (-8).toInt) fun st => st.regs.rdi.toBitVec)
  modifyIf (storeOk 1 fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (-11).toInt)
      (storeWord 1 (fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (-11).toInt) fun st => st.regs.rax.toBitVec)
  modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (-8).toInt)
      (loadReg 8 Reg64.rax (fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (-8).toInt) fun w x => w)
  modifyIf (loadOk 1 fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (-11).toInt)
      (loadReg 1 Reg64.rcx (fun st => st.regs.rsp.toBitVec + BitVec.ofInt 64 (-11).toInt) fun w x => w)
  exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra
-/
#guard_msgs in
#print redZoneLoops

end Distillery.Kraken.Tests.StackFrame
