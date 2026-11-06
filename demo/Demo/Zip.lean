import Demo.L1
import Kraken.X64.Parser
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


ascend_def zipWithAddA [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃(· = s.push64 ra)⦄ zipWithAdd ⪯[ofStateRepr abs] zipWithAddA ⦃fun _ _ => ⊤; RetRel s ra⦄
  ascend [refines_cfg (p := zipWithAdd)] with finish

/-- The synthesized L1 program: the text over the abstract machine, block by block. -/
example [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    zipWithAddA s ra = cfgLoop (Table.get [
      (.entry, do
        branch (fun st => CondCode.le.cmp (st.regs.get64 .rcx &&& st.regs.get64 .rcx) 0) (.label "LBB0_3")
        modifyIf (fun _ => True) (xorReg32Reg32 .rax .rax)
        pure ()),
      (.label "LBB0_2", do
        modifyIf (loadOk8 .rsi .rax 0) (movRegSib8 .r8 .rsi .rax 0)
        modifyIf (loadOk8 .rdi .rax 0) (addRegSib8 .r8 .rdi .rax 0)
        modifyIf (storeOk8 .rdx .rax 0) (movSib8Reg .rdx .rax 0 .r8)
        modifyIf (fun _ => True) (incReg .rax)
        branch (fun st => CondCode.nz.cmp (st.regs.get64 .rcx) (st.regs.get64 .rax)) (.label "LBB0_2")
        pure ()),
      (.label "LBB0_3", exitIf retOk ret .exit)]) (Program.next zipWithAdd) .entry := rfl
