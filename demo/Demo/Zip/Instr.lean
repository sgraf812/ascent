import Demo.Instr
import Distillery.Tactic.VCGen.Command

/-!
# `zipWithAdd`

The x64 text that clang emits for

```c
void zipWithAdd(const long *a, const long *b, long *out, long n) {
  for (long i = 0; i < n; i++)
    out[i] = a[i] + b[i];
}
```

with `-O1 -fno-vectorize -fno-unroll-loops`, and its refinement to the abstract machine.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

/-
  testq %rcx, %rcx
  jle LBB0_3
  xorl %eax, %eax
LBB0_2:
  movq (%rsi,%rax,8), %r8
  addq (%rdi,%rax,8), %r8
  movq %r8, (%rdx,%rax,8)
  incq %rax
  cmpq %rax, %rcx
  jne LBB0_2
LBB0_3:
  retq
-/
def zipWithAdd : Program := [
  .instr (.regular .W64 .W64 (.test (.reg (.low .rcx .W64)) (.regOrMem (.reg (.low .rcx .W64))))),
  .instr (.regular .W64 .W64 (.jcc .le "LBB0_3")),
  .instr (.regular .W64 .W32 (.xor (.reg (.low .rax .W32)) (.regOrMem (.reg (.low .rax .W32))))),
  .label "LBB0_2",
  .instr (.regular .W64 .W64 (.mov (.reg (.low .r8 .W64)) (.regOrMem (.mem ⟨some (.reg .rsi), some ⟨.rax, .W64⟩, .int64 0⟩)))),
  .instr (.regular .W64 .W64 (.add (.reg (.low .r8 .W64)) (.regOrMem (.mem ⟨some (.reg .rdi), some ⟨.rax, .W64⟩, .int64 0⟩)))),
  .instr (.regular .W64 .W64 (.mov (.mem ⟨some (.reg .rdx), some ⟨.rax, .W64⟩, .int64 0⟩) (.regOrMem (.reg (.low .r8 .W64))))),
  .instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64)))),
  .instr (.regular .W64 .W64 (.cmp (.reg (.low .rcx .W64)) (.regOrMem (.reg (.low .rax .W64))))),
  .instr (.regular .W64 .W64 (.jcc .nz "LBB0_2")),
  .label "LBB0_3",
  .instr (.regular .W64 .W64 .ret)]

attribute [local vcgen_simp] zipWithAdd



distill_def zipWithAddInstr [Host] [FunDecls] [Embeds zipWithAdd] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ zipWithAdd ⪯[ofStateRepr abs] zipWithAddInstr ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  distill [refines_cfg (p := zipWithAdd) (habs := abs_regs)] with finish


/--
info: def zipWithAddInstr : [Host] → BitVec 64 → Int64 → BlockM MachineData Unit :=
fun [Host] r₀ ra =>
  Program.loop zipWithAdd r₀
    (Table.get
      [({ label := none, idx := 0,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.test (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))))),
                  Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.le "LBB0_3")),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W32
                      (Operation.xor (RegOrMem.reg (Reg.low Reg64.rax Width.W32))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W32)))))],
              next := some "LBB0_2" }.label,
          do
          branch (stayIn r₀) (fun st => CondCode.le.cmp (st.regs.get64 Reg64.rcx &&& st.regs.get64 Reg64.rcx) 0)
              (label "LBB0_3")
          modifyIf (fun x => True)
              (setReg64 Reg64.rax fun st =>
                BitVec.setWidth 64 ((st.regs.get64 Reg64.rax).take 32 ^^^ (st.regs.get64 Reg64.rax).take 32))
          pure PUnit.unit),
        ({ label := some "LBB0_2", idx := 1,
              body :=
                [Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.mov (RegOrMem.reg (Reg.low Reg64.r8 Width.W64))
                        (Operand.regOrMem
                          (RegOrMem.mem
                            { base := some (RegOrRip.reg Reg64.rsi),
                              idx := some { reg := Reg64.rax, scale := Width.W64 } })))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.add (RegOrMem.reg (Reg.low Reg64.r8 Width.W64))
                        (Operand.regOrMem
                          (RegOrMem.mem
                            { base := some (RegOrRip.reg Reg64.rdi),
                              idx := some { reg := Reg64.rax, scale := Width.W64 } })))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.mov
                        (RegOrMem.mem
                          { base := some (RegOrRip.reg Reg64.rdx),
                            idx := some { reg := Reg64.rax, scale := Width.W64 } })
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.r8 Width.W64))))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64 (Operation.inc (RegOrMem.reg (Reg.low Reg64.rax Width.W64)))),
                  Directive.instr
                    (Instr.regular Width.W64 Width.W64
                      (Operation.cmp (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))
                        (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64))))),
                  Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "LBB0_2"))],
              next := some "LBB0_3" }.label,
          do
          modifyIf (loadOk 8 (sib 8 Reg64.rsi Reg64.rax 0))
              (loadReg 8 Reg64.r8 (sib 8 Reg64.rsi Reg64.rax 0) fun w x => w)
          modifyIf (loadOk 8 (sib 8 Reg64.rdi Reg64.rax 0))
              (loadReg 8 Reg64.r8 (sib 8 Reg64.rdi Reg64.rax 0) fun w st => w + st.regs.get64 Reg64.r8)
          modifyIf (storeOk 8 (sib 8 Reg64.rdx Reg64.rax 0))
              (storeWord 8 (sib 8 Reg64.rdx Reg64.rax 0) fun st => st.regs.get64 Reg64.r8)
          modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.get64 Reg64.rax + 1)
          branch (stayIn r₀) (fun st => CondCode.nz.cmp (st.regs.get64 Reg64.rcx) (st.regs.get64 Reg64.rax))
              (label "LBB0_2")
          pure PUnit.unit),
        ({ label := some "LBB0_3", idx := 2,
              body := [Directive.instr (Instr.regular Width.W64 Width.W64 Operation.ret)], next := none }.label,
          exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8) ra)])
-/
#guard_msgs in
#print zipWithAddInstr
