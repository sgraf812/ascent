import Demo.L1
import Kraken.X64.Parser
import Kraken.X64.PrettyPrint
import Ascent.Tactic.VCGen.Command

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

open Kraken.X64.Parser Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken

def bsearch : Program := parse("
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
")

attribute [local vcgen_simp] bsearch

ascend_def bsearchA [Host] [FunDecls] [Embeds bsearch] (s : MachineData) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃(· = s.push64 ra)⦄ bsearch ⪯[ofStateRepr abs] bsearchA ⦃fun _ _ => ⊤; RetRel s ra⦄
  ascend [refines_cfg (p := bsearch)] with finish

/--
info: def Ascent.Kraken.bsearchA : BlockM MachineData Unit :=
cfgLoop
  (bsearch.table
    (Table.get
      [(CfgLabel.ofLabel
            { label := none, idx := 0,
                body :=
                  [asm|
                      "xor ecx, ecx"
                      "jmp LBB0_3"],
                next := some "LBB0_1" }.label,
          do
          modifyIf (fun x => True)
              (setReg64 Reg64.rcx fun st =>
                BitVec.setWidth 64 ((st.regs.get64 Reg64.rcx).take 32 ^^^ (st.regs.get64 Reg64.rcx).take 32))
          branch (fun x => true) (CfgLabel.label "LBB0_3")),
        (CfgLabel.ofLabel
            { label := some "LBB0_1", idx := 1,
                body :=
                  [asm|
                      "inc r8"
                      "mov r9b, 1"
                      "mov rcx, r8"],
                next := some "LBB0_2" }.label,
          do
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.get64 Reg64.r8 + 1)
          modifyIf (fun x => True)
              (setReg64 Reg64.r9 fun st => (st.regs.get64 Reg64.r9).replaceLow (BitVec.setWidth 8 (Int64.toBitVec 1)))
          modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.get64 Reg64.r8)
          pure PUnit.unit),
        (CfgLabel.ofLabel
            { label := some "LBB0_2", idx := 2,
                body :=
                  [asm|
                      "test r9b, r9b"
                      "je LBB0_9"],
                next := some "LBB0_3" }.label,
          do
          branch
              (fun st =>
                CondCode.z.interp
                  (StatusFlags.from_result ((st.regs.get64 Reg64.r9).take 8 &&& (st.regs.get64 Reg64.r9).take 8)
                    { cf := false, af := false, of := false }))
              (CfgLabel.label "LBB0_9")
          pure PUnit.unit),
        (CfgLabel.ofLabel
            { label := some "LBB0_3", idx := 3,
                body :=
                  [asm|
                      "mov r8, rsi"
                      "sub r8, rcx"
                      "jbe LBB0_8"
                      "shr r8, 1"
                      "add r8, rcx"
                      "mov r9, QWORD PTR [rdi+r8*8+0]"
                      "cmp r9, rdx"
                      "jl LBB0_1"
                      "jle LBB0_7"
                      "mov r9b, 1"
                      "mov rsi, r8"
                      "jmp LBB0_2"],
                next := some "LBB0_7" }.label,
          do
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.get64 Reg64.rsi)
          let c ← peek fun st => CondCode.be.cmp (st.regs.get64 Reg64.r8) (st.regs.get64 Reg64.rcx)
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.get64 Reg64.r8 - st.regs.get64 Reg64.rcx)
          branch (fun x => c) (CfgLabel.label "LBB0_8")
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => (st.regs.get64 Reg64.r8).ushiftRight 1)
          modifyIf (fun x => True) (setReg64 Reg64.r8 fun st => st.regs.get64 Reg64.rcx + st.regs.get64 Reg64.r8)
          modifyIf (loadOk 8 (sib 8 Reg64.rdi Reg64.r8 0))
              (loadReg 8 Reg64.r9 (sib 8 Reg64.rdi Reg64.r8 0) fun w x => w)
          branch (fun st => CondCode.l.cmp (st.regs.get64 Reg64.r9) (st.regs.get64 Reg64.rdx)) (CfgLabel.label "LBB0_1")
          branch (fun st => CondCode.le.cmp (st.regs.get64 Reg64.r9) (st.regs.get64 Reg64.rdx))
              (CfgLabel.label "LBB0_7")
          modifyIf (fun x => True)
              (setReg64 Reg64.r9 fun st => (st.regs.get64 Reg64.r9).replaceLow (BitVec.setWidth 8 (Int64.toBitVec 1)))
          modifyIf (fun x => True) (setReg64 Reg64.rsi fun st => st.regs.get64 Reg64.r8)
          branch (fun x => true) (CfgLabel.label "LBB0_2")),
        (CfgLabel.ofLabel
            { label := some "LBB0_7", idx := 4,
                body :=
                  [asm|
                      "xor r9d, r9d"
                      "mov rax, r8"
                      "jmp LBB0_2"],
                next := some "LBB0_8" }.label,
          do
          modifyIf (fun x => True)
              (setReg64 Reg64.r9 fun st =>
                BitVec.setWidth 64 ((st.regs.get64 Reg64.r9).take 32 ^^^ (st.regs.get64 Reg64.r9).take 32))
          modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.get64 Reg64.r8)
          branch (fun x => true) (CfgLabel.label "LBB0_2")),
        (CfgLabel.ofLabel
            { label := some "LBB0_8", idx := 5,
                body :=
                  [asm|
                      "mov rax, -1"],
                next := some "LBB0_9" }.label,
          do
          modifyIf (fun x => True) (setReg64 Reg64.rax fun x => BitVec.setWidth 64 (-1).toBitVec)
          pure PUnit.unit),
        (CfgLabel.ofLabel
            { label := some "LBB0_9", idx := 6,
                body :=
                  [asm|
                      "ret"],
                next := none }.label,
          exitIf (loadOk 8 fun st => st.regs.get64 Reg64.rsp) (setReg64 Reg64.rsp fun st => st.regs.get64 Reg64.rsp + 8)
            CfgLabel.exit)]))
  CfgLabel.entry
-/
#guard_msgs in
#print bsearchA

end Ascent.Kraken
