import Demo.L1
import Kraken.X64.Parser
import Kraken.X64.PrettyPrint
import Ascent.Tactic.VCGen.Command

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

open Kraken.X64.Parser Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

def zipWithAdd : Program := parse("
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
")

attribute [local vcgen_simp] zipWithAdd



ascend_def zipWithAddA [Host] [FunDecls] [Embeds zipWithAdd] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ zipWithAdd ⪯[ofStateRepr abs] zipWithAddA ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  ascend [refines_cfg (p := zipWithAdd) (habs := abs_regs)] with finish


/--
info: def zipWithAddA : [Host] → BitVec 64 → Int64 → BlockM MachineData Unit :=
fun [Host] r₀ ra =>
  Program.loop zipWithAdd r₀
    (Table.get
      [({ label := none, idx := 0,
              body :=
                [asm|
                    "test rcx, rcx"
                    "jle LBB0_3"
                    "xor eax, eax"],
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
                [asm|
                    "mov r8, QWORD PTR [rsi+rax*8+0]"
                    "add r8, QWORD PTR [rdi+rax*8+0]"
                    "mov QWORD PTR [rdx+rax*8+0], r8"
                    "inc rax"
                    "cmp rcx, rax"
                    "jne LBB0_2"],
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
              body :=
                [asm|
                    "ret"],
              next := none }.label,
          exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8) ra)])
-/
#guard_msgs in
#print zipWithAddA
