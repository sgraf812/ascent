import Demo.L1
import Kraken.X64.Parser
import Kraken.X64.PrettyPrint
import Ascent.Tactic.VCGen.Command

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

open Kraken.X64.Parser Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken

def memmove : Program := parse("
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
")

attribute [local vcgen_simp] memmove

ascend_def memmoveA [Host] [FunDecls] [Embeds memmove] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ memmove ⪯[ofStateRepr abs] memmoveA ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  ascend [refines_cfg (p := memmove) (habs := abs_regs)] with finish


/--
info: def Ascent.Kraken.memmoveA : [Host] → BitVec 64 → Int64 → BlockM MachineData Unit :=
fun [Host] r₀ ra =>
  Program.loop memmove r₀
    (Table.get
      [({ label := none, idx := 0,
              body :=
                [asm|
                    "mov rax, rdi"
                    "cmp rdi, rsi"
                    "jae LBB0_1"
                    "test rdx, rdx"
                    "je LBB0_7"
                    "xor ecx, ecx"],
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
                [asm|
                    "movzx edi, BYTE PTR [rsi+rcx*1+0]"
                    "mov BYTE PTR [rax+rcx*1+0], dil"
                    "inc rcx"
                    "cmp rdx, rcx"
                    "jne LBB0_6"
                    "jmp LBB0_7"],
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
                [asm|
                    "test rdx, rdx"
                    "je LBB0_7"
                    "mov rcx, rdx"],
              next := some "LBB0_3" }.label,
          do
          branch (stayIn r₀) (fun st => CondCode.z.cmp (st.regs.get64 Reg64.rdx &&& st.regs.get64 Reg64.rdx) 0)
              (label "LBB0_7")
          modifyIf (fun x => True) (setReg64 Reg64.rcx fun st => st.regs.get64 Reg64.rdx)
          pure PUnit.unit),
        ({ label := some "LBB0_3", idx := 3,
              body :=
                [asm|
                    "dec rcx"
                    "movzx edi, BYTE PTR [rsi+rdx*1+-1]"
                    "mov BYTE PTR [rax+rdx*1+-1], dil"
                    "mov rdx, rcx"
                    "jne LBB0_3"],
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
              body :=
                [asm|
                    "ret"],
              next := none }.label,
          exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8) ra)])
-/
#guard_msgs in
#print memmoveA

end Ascent.Kraken
