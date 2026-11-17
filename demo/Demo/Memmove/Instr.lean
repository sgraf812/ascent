import Demo.Instr
import Distillery.Tactic.VCGen.Command

/-!
# `memmove`

The x64 text that clang emits for

```c
void *memmove_(void *dst, const void *src, unsigned long n) {
  unsigned char *d = dst;
  const unsigned char *s = src;
  if (d < s) {
    for (unsigned long i = 0; i < n; i++) d[i] = s[i];
  } else {
    for (unsigned long i = n; i > 0; i--) d[i - 1] = s[i - 1];
  }
  return dst;
}
```

with `-O1 -fno-vectorize -fno-unroll-loops -fno-builtin -fomit-frame-pointer`, and its refinement to
the abstract machine. The backward loop branches on the flag that `decq %rcx` writes, after three
instructions that leave the flags unchanged.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

namespace Distillery.Kraken

/-
  movq %rdi, %rax
  cmpq %rsi, %rdi
  jae LBB0_1
  testq %rdx, %rdx
  je LBB0_7
  xorl %ecx, %ecx
LBB0_6:
  movzbl (%rsi,%rcx), %edi
  movb %dil, (%rax,%rcx)
  incq %rcx
  cmpq %rcx, %rdx
  jne LBB0_6
  jmp LBB0_7
LBB0_1:
  testq %rdx, %rdx
  je LBB0_7
  movq %rdx, %rcx
LBB0_3:
  decq %rcx
  movzbl -1(%rsi,%rdx), %edi
  movb %dil, -1(%rax,%rdx)
  movq %rcx, %rdx
  jne LBB0_3
LBB0_7:
  retq
-/
def memmove : Program := [
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rdi .W64))))),
  .instr (.regular .W64 .W64 (.cmp (.reg (.low .rdi .W64)) (.regOrMem (.reg (.low .rsi .W64))))),
  .instr (.regular .W64 .W64 (.jcc .nc "LBB0_1")),
  .instr (.regular .W64 .W64 (.test (.reg (.low .rdx .W64)) (.regOrMem (.reg (.low .rdx .W64))))),
  .instr (.regular .W64 .W64 (.jcc .z "LBB0_7")),
  .instr (.regular .W64 .W32 (.xor (.reg (.low .rcx .W32)) (.regOrMem (.reg (.low .rcx .W32))))),
  .label "LBB0_6",
  .instr (.regular .W64 .W32 (.movzx (w' := .W8) (.reg (.low .rdi .W32)) (.mem ⟨some (.reg .rsi), some ⟨.rcx, .W8⟩, .int64 0⟩))),
  .instr (.regular .W64 .W8 (.mov (.mem ⟨some (.reg .rax), some ⟨.rcx, .W8⟩, .int64 0⟩) (.regOrMem (.reg (.low .rdi .W8))))),
  .instr (.regular .W64 .W64 (.inc (.reg (.low .rcx .W64)))),
  .instr (.regular .W64 .W64 (.cmp (.reg (.low .rdx .W64)) (.regOrMem (.reg (.low .rcx .W64))))),
  .instr (.regular .W64 .W64 (.jcc .nz "LBB0_6")),
  .instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label "LBB0_7") .after_current_instruction)))),
  .label "LBB0_1",
  .instr (.regular .W64 .W64 (.test (.reg (.low .rdx .W64)) (.regOrMem (.reg (.low .rdx .W64))))),
  .instr (.regular .W64 .W64 (.jcc .z "LBB0_7")),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rcx .W64)) (.regOrMem (.reg (.low .rdx .W64))))),
  .label "LBB0_3",
  .instr (.regular .W64 .W64 (.dec (.reg (.low .rcx .W64)))),
  .instr (.regular .W64 .W32 (.movzx (w' := .W8) (.reg (.low .rdi .W32)) (.mem ⟨some (.reg .rsi), some ⟨.rdx, .W8⟩, .int64 (-1)⟩))),
  .instr (.regular .W64 .W8 (.mov (.mem ⟨some (.reg .rax), some ⟨.rdx, .W8⟩, .int64 (-1)⟩) (.regOrMem (.reg (.low .rdi .W8))))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rdx .W64)) (.regOrMem (.reg (.low .rcx .W64))))),
  .instr (.regular .W64 .W64 (.jcc .nz "LBB0_3")),
  .label "LBB0_7",
  .instr (.regular .W64 .W64 .ret)]

attribute [local vcgen_simp] memmove

distill_def memmoveInstr [Host] [FunDecls] [Embeds memmove] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ memmove ⪯[ofStateRepr abs] memmoveInstr ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  distill [refines_cfg (p := memmove) (habs := abs_regs)] with finish


/--
info: def Distillery.Kraken.memmoveInstr : [Host] → BitVec 64 → Int64 → BlockM MachineData Unit :=
fun [Host] r₀ ra =>
  Program.loop memmove r₀
    (Table.get
      [({ label := none, idx := 0,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rdi Width.W64))))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.cmp (RegOrMem.reg (Reg.low Reg64.rdi Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rsi Width.W64))))),
                  Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nc "LBB0_1")),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.test (RegOrMem.reg (Reg.low Reg64.rdx Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rdx Width.W64))))),
                  Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.z "LBB0_7")),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W32
                      (Operation.xor (RegOrMem.reg (Reg.low Reg64.rcx Width.W32))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)))))],
              next := some "LBB0_6" }.label,
          do
          modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.get64 Reg64.rdi)
          branch (stayIn r₀) (fun st => CondCode.nc.cmp (st.regs.get64 Reg64.rdi) (st.regs.get64 Reg64.rsi))
              (label "LBB0_1")
          branch (stayIn r₀) (fun st => CondCode.z.cmp (st.regs.get64 Reg64.rdx &&& st.regs.get64 Reg64.rdx) 0)
              (label "LBB0_7")
          modifyIf (fun x => True)
              (setReg64 Reg64.rcx fun st =>
                BitVec.setWidth 64 ((st.regs.get64 Reg64.rcx).take 32 ^^^ (st.regs.get64 Reg64.rcx).take 32))
          pure PUnit.unit),
        ({ label := some "LBB0_6", idx := 1,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W32
                      (Operation.movzx (RegOrMem.reg (Reg.low Reg64.rdi Width.W32))
                        (RegOrMem.mem
                          { base := some (RegOrRip.reg Reg64.rsi),
                            idx := some { reg := Reg64.rcx, scale := Width.W8 } }))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W8
                      (Operation.mov
                        (RegOrMem.mem
                          { base := some (RegOrRip.reg Reg64.rax),
                            idx := some { reg := Reg64.rcx, scale := Width.W8 } })
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rdi Width.W8))))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64 (Operation.inc (RegOrMem.reg (Reg.low Reg64.rcx Width.W64)))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.cmp (RegOrMem.reg (Reg.low Reg64.rdx Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))))),
                  Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "LBB0_6")),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.jmp
                        (RelRegOrMem.rel ((ConstExpr.label "LBB0_7").sub ConstExpr.after_current_instruction))))],
              next := some "LBB0_1" }.label,
          do
          modifyIf (loadOk 1 (sib 1 Reg64.rsi Reg64.rcx 0))
              (loadReg 1 Reg64.rdi (sib 1 Reg64.rsi Reg64.rcx 0) fun w x => w)
          modifyIf (storeOk 1 (sib 1 Reg64.rax Reg64.rcx 0))
              (storeWord 1 (sib 1 Reg64.rax Reg64.rcx 0) fun st => st.regs.get64 Reg64.rdi)
          modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.get64 Reg64.rcx + 1)
          branch (stayIn r₀) (fun st => CondCode.nz.cmp (st.regs.get64 Reg64.rdx) (st.regs.get64 Reg64.rcx))
              (label "LBB0_6")
          branch (stayIn r₀) (fun x => true) (label "LBB0_7")),
        ({ label := some "LBB0_1", idx := 2,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.test (RegOrMem.reg (Reg.low Reg64.rdx Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rdx Width.W64))))),
                  Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.z "LBB0_7")),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rdx Width.W64)))))],
              next := some "LBB0_3" }.label,
          do
          branch (stayIn r₀) (fun st => CondCode.z.cmp (st.regs.get64 Reg64.rdx &&& st.regs.get64 Reg64.rdx) 0)
              (label "LBB0_7")
          modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.get64 Reg64.rdx)
          pure PUnit.unit),
        ({ label := some "LBB0_3", idx := 3,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W64 (Operation.dec (RegOrMem.reg (Reg.low Reg64.rcx Width.W64)))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W32
                      (Operation.movzx (RegOrMem.reg (Reg.low Reg64.rdi Width.W32))
                        (RegOrMem.mem
                          { base := some (RegOrRip.reg Reg64.rsi), idx := some { reg := Reg64.rdx, scale := Width.W8 },
                            disp := ConstExpr.int64 (-1) }))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W8
                      (Operation.mov
                        (RegOrMem.mem
                          { base := some (RegOrRip.reg Reg64.rax), idx := some { reg := Reg64.rdx, scale := Width.W8 },
                            disp := ConstExpr.int64 (-1) })
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rdi Width.W8))))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.rdx Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))))),
                  Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "LBB0_3"))],
              next := some "LBB0_7" }.label,
          do
          let x ←
            do
              let z ← peek fun st => st.regs.get64 Reg64.rcx - 1 == BitVec.zero 64
              modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.get64 Reg64.rcx - 1)
              pure z
          modifyIf (loadOk 1 (sib 1 Reg64.rsi Reg64.rdx (-1)))
              (loadReg 1 Reg64.rdi (sib 1 Reg64.rsi Reg64.rdx (-1)) fun w x => w)
          modifyIf (storeOk 1 (sib 1 Reg64.rax Reg64.rdx (-1)))
              (storeWord 1 (sib 1 Reg64.rax Reg64.rdx (-1)) fun st => st.regs.get64 Reg64.rdi)
          modifyIf (fun x => True) (setReg64 Reg64.rdx fun st => st.regs.get64 Reg64.rcx)
          branch (stayIn r₀) (fun x_1 => !x) (label "LBB0_3")
          pure PUnit.unit),
        ({ label := some "LBB0_7", idx := 4,
              body := [Directive.instr (Instr.regular Width.W64 Width.W64 Operation.ret)], next := none }.label,
          exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8) ra)])
-/
#guard_msgs in
#print memmoveInstr

end Distillery.Kraken
