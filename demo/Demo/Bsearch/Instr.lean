import Demo.Instr
import Distillery.Tactic.VCGen.Command

/-!
# Binary search

The x64 text that clang emits for

```c
long bsearch_(const long *a, unsigned long n, long key) {
  unsigned long lo = 0, hi = n;
  while (lo < hi) {
    unsigned long mid = lo + (hi - lo) / 2;
    if (a[mid] < key) lo = mid + 1;
    else if (a[mid] > key) hi = mid;
    else return (long)mid;
  }
  return -1;
}
```

with `-O1 -fno-vectorize -fno-unroll-loops -fno-builtin -fomit-frame-pointer`, and its refinement to
the abstract machine. The loop has several blocks: the header `LBB0_3` returns through `LBB0_1` or
`LBB0_7` and then `LBB0_2`. One `cmpq` feeds two jumps, `jl` and `jle`, and the byte register `r9b`
records whether the loop continues.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

namespace Distillery.Kraken

/-
  xorl %ecx, %ecx
  jmp LBB0_3
LBB0_1:
  incq %r8
  movb $1, %r9b
  movq %r8, %rcx
LBB0_2:
  testb %r9b, %r9b
  je LBB0_9
LBB0_3:
  movq %rsi, %r8
  subq %rcx, %r8
  jbe LBB0_8
  shrq %r8
  addq %rcx, %r8
  movq (%rdi,%r8,8), %r9
  cmpq %rdx, %r9
  jl LBB0_1
  jle LBB0_7
  movb $1, %r9b
  movq %r8, %rsi
  jmp LBB0_2
LBB0_7:
  xorl %r9d, %r9d
  movq %r8, %rax
  jmp LBB0_2
LBB0_8:
  movq $-1, %rax
LBB0_9:
  retq
-/
def bsearch : Program := [
  .instr (.regular .W64 .W32 (.xor (.reg (.low .rcx .W32)) (.regOrMem (.reg (.low .rcx .W32))))),
  .instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label "LBB0_3") .after_current_instruction)))),
  .label "LBB0_1",
  .instr (.regular .W64 .W64 (.inc (.reg (.low .r8 .W64)))),
  .instr (.regular .W64 .W8 (.mov (.reg (.low .r9 .W8)) (.imm (.int64 1)))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rcx .W64)) (.regOrMem (.reg (.low .r8 .W64))))),
  .label "LBB0_2",
  .instr (.regular .W64 .W8 (.test (.reg (.low .r9 .W8)) (.regOrMem (.reg (.low .r9 .W8))))),
  .instr (.regular .W64 .W64 (.jcc .z "LBB0_9")),
  .label "LBB0_3",
  .instr (.regular .W64 .W64 (.mov (.reg (.low .r8 .W64)) (.regOrMem (.reg (.low .rsi .W64))))),
  .instr (.regular .W64 .W64 (.sub (.reg (.low .r8 .W64)) (.regOrMem (.reg (.low .rcx .W64))))),
  .instr (.regular .W64 .W64 (.jcc .be "LBB0_8")),
  .instr (.regular .W64 .W64 (.shr (.reg (.low .r8 .W64)) (.imm8 (.int64 1)))),
  .instr (.regular .W64 .W64 (.add (.reg (.low .r8 .W64)) (.regOrMem (.reg (.low .rcx .W64))))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .r9 .W64)) (.regOrMem (.mem ⟨some (.reg .rdi), some ⟨.r8, .W64⟩, .int64 0⟩)))),
  .instr (.regular .W64 .W64 (.cmp (.reg (.low .r9 .W64)) (.regOrMem (.reg (.low .rdx .W64))))),
  .instr (.regular .W64 .W64 (.jcc .l "LBB0_1")),
  .instr (.regular .W64 .W64 (.jcc .le "LBB0_7")),
  .instr (.regular .W64 .W8 (.mov (.reg (.low .r9 .W8)) (.imm (.int64 1)))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rsi .W64)) (.regOrMem (.reg (.low .r8 .W64))))),
  .instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label "LBB0_2") .after_current_instruction)))),
  .label "LBB0_7",
  .instr (.regular .W64 .W32 (.xor (.reg (.low .r9 .W32)) (.regOrMem (.reg (.low .r9 .W32))))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .r8 .W64))))),
  .instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label "LBB0_2") .after_current_instruction)))),
  .label "LBB0_8",
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.imm (.int64 (-1))))),
  .label "LBB0_9",
  .instr (.regular .W64 .W64 .ret)]

attribute [local vcgen_simp] bsearch

distill_def bsearchInstr [Host] [FunDecls] [Embeds bsearch] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ bsearch ⪯[ofStateRepr abs] bsearchInstr ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  distill [refines_cfg (p := bsearch) (habs := abs_regs)] with finish



/--
info: def Distillery.Kraken.bsearchInstr : [Host] → BitVec 64 → Int64 → BlockM MachineData Unit :=
fun [Host] r₀ ra =>
  Program.loop bsearch r₀
    (Table.get
      [({ label := none, idx := 0,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W32
                      (Operation.xor (RegOrMem.reg (Reg.low Reg64.rcx Width.W32))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rcx Width.W32))))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.jmp
                        (RelRegOrMem.rel ((ConstExpr.label "LBB0_3").sub ConstExpr.after_current_instruction))))],
              next := some "LBB0_1" }.label,
          do
          modifyIf (fun x => True)
              (setReg64 Reg64.rcx fun st =>
                BitVec.setWidth 64 ((st.regs.get64 Reg64.rcx).take 32 ^^^ (st.regs.get64 Reg64.rcx).take 32))
          branch (stayIn r₀) (fun x => true) (label "LBB0_3")),
        ({ label := some "LBB0_1", idx := 1,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W64 (Operation.inc (RegOrMem.reg (Reg.low Reg64.r8 Width.W64)))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W8
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.r9 Width.W8)) (Operand.imm (ConstExpr.int64 1)))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.r8 Width.W64)))))],
              next := some "LBB0_2" }.label,
          do
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.get64 Reg64.r8 + 1)
          modifyIf (fun x => True)
              (setReg64 Reg64.r9 fun st => (st.regs.get64 Reg64.r9).replaceLow (BitVec.setWidth 8 (Int64.toBitVec 1)))
          modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.get64 Reg64.r8)
          pure PUnit.unit),
        ({ label := some "LBB0_2", idx := 2,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W8
                      (Operation.test (RegOrMem.reg (Reg.low Reg64.r9 Width.W8))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.r9 Width.W8))))),
                  Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.z "LBB0_9"))],
              next := some "LBB0_3" }.label,
          do
          branch (stayIn r₀)
              (fun st =>
                CondCode.z.interp
                  (StatusFlags.from_result ((st.regs.get64 Reg64.r9).take 8 &&& (st.regs.get64 Reg64.r9).take 8)
                    { cf := false, af := false, of := false }))
              (label "LBB0_9")
          pure PUnit.unit),
        ({ label := some "LBB0_3", idx := 3,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.r8 Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rsi Width.W64))))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.sub (RegOrMem.reg (Reg.low Reg64.r8 Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))))),
                  Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.be "LBB0_8")),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.shr (RegOrMem.reg (Reg.low Reg64.r8 Width.W64))
                        (ShiftCountExpr.imm8 (ConstExpr.int64 1)))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.add (RegOrMem.reg (Reg.low Reg64.r8 Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.r9 Width.W64))
                        (Operand.regOrMem
                          (RegOrMem.mem
                            { base := some (RegOrRip.reg Reg64.rdi),
                              idx := some { reg := Reg64.r8, scale := Width.W64 } })))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.cmp (RegOrMem.reg (Reg.low Reg64.r9 Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rdx Width.W64))))),
                  Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.l "LBB0_1")),
                  Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.le "LBB0_7")),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W8
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.r9 Width.W8)) (Operand.imm (ConstExpr.int64 1)))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.rsi Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.r8 Width.W64))))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.jmp
                        (RelRegOrMem.rel ((ConstExpr.label "LBB0_2").sub ConstExpr.after_current_instruction))))],
              next := some "LBB0_7" }.label,
          do
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.get64 Reg64.rsi)
          let c ← peek fun st => CondCode.be.cmp (st.regs.get64 Reg64.r8) (st.regs.get64 Reg64.rcx)
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.get64 Reg64.r8 - st.regs.get64 Reg64.rcx)
          branch (stayIn r₀) (fun x => c) (label "LBB0_8")
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => (st.regs.get64 Reg64.r8).ushiftRight 1)
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.get64 Reg64.rcx + st.regs.get64 Reg64.r8)
          modifyIf (loadOk 8 (sib 8 Reg64.rdi Reg64.r8 0))
              (loadReg 8 Reg64.r9 (sib 8 Reg64.rdi Reg64.r8 0) fun w x => w)
          branch (stayIn r₀) (fun st => CondCode.l.cmp (st.regs.get64 Reg64.r9) (st.regs.get64 Reg64.rdx))
              (label "LBB0_1")
          branch (stayIn r₀) (fun st => CondCode.le.cmp (st.regs.get64 Reg64.r9) (st.regs.get64 Reg64.rdx))
              (label "LBB0_7")
          modifyIf (fun x => True)
              (setReg64 Reg64.r9 fun st => (st.regs.get64 Reg64.r9).replaceLow (BitVec.setWidth 8 (Int64.toBitVec 1)))
          modifyIf (fun x => True) (setReg64 Reg64.rsi fun st => st.regs.get64 Reg64.r8)
          branch (stayIn r₀) (fun x => true) (label "LBB0_2")),
        ({ label := some "LBB0_7", idx := 4,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W32
                      (Operation.xor (RegOrMem.reg (Reg.low Reg64.r9 Width.W32))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.r9 Width.W32))))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.r8 Width.W64))))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.jmp
                        (RelRegOrMem.rel ((ConstExpr.label "LBB0_2").sub ConstExpr.after_current_instruction))))],
              next := some "LBB0_8" }.label,
          do
          modifyIf (fun x => True)
              (setReg64 Reg64.r9 fun st =>
                BitVec.setWidth 64 ((st.regs.get64 Reg64.r9).take 32 ^^^ (st.regs.get64 Reg64.r9).take 32))
          modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.get64 Reg64.r8)
          branch (stayIn r₀) (fun x => true) (label "LBB0_2")),
        ({ label := some "LBB0_8", idx := 5,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
                        (Operand.imm (ConstExpr.int64 (-1)))))],
              next := some "LBB0_9" }.label,
          do
          modifyIf (fun x => True) (setReg64 Reg64.rax fun x => BitVec.setWidth 64 (-1).toBitVec)
          pure PUnit.unit),
        ({ label := some "LBB0_9", idx := 6,
              body := [Directive.instr (Instr.regular Width.W64 Width.W64 Operation.ret)], next := none }.label,
          exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8) ra)])
-/
#guard_msgs in
#print bsearchInstr

end Distillery.Kraken
