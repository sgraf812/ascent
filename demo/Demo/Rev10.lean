import Demo.CfgRewrite
import Kraken.X64.Parser
import Kraken.X64.PrettyPrint
import Ascent.Tactic.VCGen.Command

/-!
# `rev10`

A leaf function that saves and restores callee-saved registers. The x64 text that clang emits for

```c
void rev10(long *a) {
  long s0 = a[0], s1 = a[1], s2 = a[2], s3 = a[3], s4 = a[4], s5 = a[5], s6 = a[6], s7 = a[7], s8 = a[8], s9 = a[9];
  a[0] = s9; a[1] = s8; a[2] = s7; a[3] = s6; a[4] = s5; a[5] = s4; a[6] = s3; a[7] = s2; a[8] = s1; a[9] = s0;
}
```

with `-O1 -fno-vectorize -fno-unroll-loops -fno-builtin -fomit-frame-pointer`, and its refinement to
the abstract machine. The ten words need two registers beyond the caller-saved ones, so the text pushes
`r14` and `rbx` on entry and pops them before the return.
-/

open Kraken.X64.Parser Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken

def rev10 : Program := parse("
  pushq %r14
  pushq %rbx
  movq (%rdi), %rax
  movq 8(%rdi), %rcx
  movq 16(%rdi), %rdx
  movq 24(%rdi), %rsi
  movq 32(%rdi), %r8
  movq 40(%rdi), %r9
  movq 48(%rdi), %r10
  movq 56(%rdi), %r11
  movq 64(%rdi), %rbx
  movq 72(%rdi), %r14
  movq %r14, (%rdi)
  movq %rbx, 8(%rdi)
  movq %r11, 16(%rdi)
  movq %r10, 24(%rdi)
  movq %r9, 32(%rdi)
  movq %r8, 40(%rdi)
  movq %rsi, 48(%rdi)
  movq %rdx, 56(%rdi)
  movq %rcx, 64(%rdi)
  movq %rax, 72(%rdi)
  popq %rbx
  popq %r14
  retq
")

attribute [local vcgen_simp] rev10

ascend_def rev10A [Host] [FunDecls] [Embeds rev10] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ rev10 ⪯[ofStateRepr abs] rev10A ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  ascend [refines_cfg (p := rev10) (habs := abs_regs)] with finish

sym_simp_def rev10T [Host] [Embeds rev10] (r₀ : BitVec 64) (ra : Int64) : BlockM MachineData Unit from rev10A r₀ ra
  using pre [] post [rev10A, rev10, Program.loop, Program.entryNext, Program.firstLabel, Program.table,
    Program.blocks, List.filterMap_cons, List.filterMap_nil, List.reverse_nil, Table.get_cons,
    Option.some.injEq, reduceCtorEq, jumpTo_none, cfgLoop_eq_throw, Table.get?_nil, tryCatch_bind_assoc,
    tryCatch_modifyIf_bind, tryCatch_exitIf_cfgLoop, stayIn_setReg64_rsp, BitVec.reduceSLT, Bool.not_true,
    eq_self_iff_true, implies_true, bind_assoc, AInstr.exitIf_bind, bind_pure_unit, pure_bind]

theorem rev10T.refines [Host] [FunDecls] [Embeds rev10] (r₀ : BitVec 64) (ra : Int64) :
    ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ rev10 ⪯[ofStateRepr abs] (rev10T r₀ ra) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄ :=
  rev10T.eq r₀ ra ▸ rev10A.refines r₀ ra

/--
info: def Ascent.Kraken.rev10T : BitVec 64 → Int64 → BlockM MachineData Unit :=
fun r₀ ra => do
  modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
      (storeWord 8 (fun st => st.regs.rsp.toBitVec - 8#64) fun st => st.regs.r14.toBitVec)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 8#64)
  modifyIf (storeOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
      (storeWord 8 (fun st => st.regs.rsp.toBitVec - 8#64) fun st => st.regs.rbx.toBitVec)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec - 8#64)
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec) (loadReg 8 Reg64.rax (fun st => st.regs.rdi.toBitVec) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 8))
      (loadReg 8 Reg64.rcx (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 8)) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 16))
      (loadReg 8 Reg64.rdx (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 16)) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 24))
      (loadReg 8 Reg64.rsi (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 24)) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 32))
      (loadReg 8 Reg64.r8 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 32)) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 40))
      (loadReg 8 Reg64.r9 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 40)) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 48))
      (loadReg 8 Reg64.r10 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 48)) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 56))
      (loadReg 8 Reg64.r11 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 56)) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 64))
      (loadReg 8 Reg64.rbx (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 64)) fun w x => w)
  modifyIf (loadOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 72))
      (loadReg 8 Reg64.r14 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 72)) fun w x => w)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec)
      (storeWord 8 (fun st => st.regs.rdi.toBitVec) fun st => st.regs.r14.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 8))
      (storeWord 8 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 8)) fun st => st.regs.rbx.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 16))
      (storeWord 8 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 16)) fun st => st.regs.r11.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 24))
      (storeWord 8 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 24)) fun st => st.regs.r10.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 32))
      (storeWord 8 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 32)) fun st => st.regs.r9.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 40))
      (storeWord 8 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 40)) fun st => st.regs.r8.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 48))
      (storeWord 8 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 48)) fun st => st.regs.rsi.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 56))
      (storeWord 8 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 56)) fun st => st.regs.rdx.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 64))
      (storeWord 8 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 64)) fun st => st.regs.rcx.toBitVec)
  modifyIf (storeOk 8 fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 72))
      (storeWord 8 (fun st => st.regs.rdi.toBitVec + BitVec.ofInt 64 (Int64.toInt 72)) fun st => st.regs.rax.toBitVec)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
  modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
      (loadReg 8 Reg64.rbx (fun st => st.regs.rsp.toBitVec - 8#64) fun w x => w)
  modifyIf (fun x => True) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
  modifyIf (loadOk 8 fun st => st.regs.rsp.toBitVec - 8#64)
      (loadReg 8 Reg64.r14 (fun st => st.regs.rsp.toBitVec - 8#64) fun w x => w)
  exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8#64) ra
-/
#guard_msgs in
#print rev10T

end Ascent.Kraken
