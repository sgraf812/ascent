import Demo.InstrCall
import Demo.InstrGen
import Demo.Swap.Instr

/-!
# `reverse_`

The caller of the function-call example. The x64 text that clang emits for

```c
void reverse_(long *a, unsigned long n) {
  if (n < 2) return;
  unsigned long i = 0, j = n - 1;
  while (i < j) { swap(&a[i], &a[j]); i++; j--; }
}
```

with `-O1 -fno-vectorize -fno-unroll-loops -fno-builtin -fomit-frame-pointer`. The call of `_swap`
becomes `callInstr` of the abstract callee `k`, given by its refinement for every frame and return
address.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr ofStateRel)
open scoped Program.WP

set_option experimental.vcgen true

namespace Distillery.Kraken

/-
_reverse_:
  cmpq $2, %rsi
  jb LBB1_4
  pushq %r15
  pushq %r14
  pushq %r12
  pushq %rbx
  pushq %rax
  movq %rsi, %rbx
  movq %rdi, %r14
  leaq (%rdi,%rsi,8), %r15
  addq $-8, %r15
  decq %rbx
  movl $1, %r12d
LBB1_2:
  movq %r14, %rdi
  movq %r15, %rsi
  callq _swap
  decq %rbx
  addq $-8, %r15
  addq $8, %r14
  cmpq %rbx, %r12
  leaq 1(%r12), %r12
  jb LBB1_2
  addq $8, %rsp
  popq %rbx
  popq %r12
  popq %r14
  popq %r15
LBB1_4:
  retq
-/
def reverse : Program := [
  .label "_reverse_",
  .instr (.regular .W64 .W64 (.cmp (.reg (.low .rsi .W64)) (.imm (.int64 2)))),
  .instr (.regular .W64 .W64 (.jcc .c "LBB1_4")),
  .instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low .r15 .W64))))),
  .instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low .r14 .W64))))),
  .instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low .r12 .W64))))),
  .instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low .rbx .W64))))),
  .instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low .rax .W64))))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rbx .W64)) (.regOrMem (.reg (.low .rsi .W64))))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .r14 .W64)) (.regOrMem (.reg (.low .rdi .W64))))),
  .instr (.regular .W64 .W64 (.lea (.low .r15 .W64) ⟨some (.reg .rdi), some ⟨.rsi, .W64⟩, .int64 0⟩)),
  .instr (.regular .W64 .W64 (.add (.reg (.low .r15 .W64)) (.imm (.int64 (-8))))),
  .instr (.regular .W64 .W64 (.dec (.reg (.low .rbx .W64)))),
  .instr (.regular .W64 .W32 (.mov (.reg (.low .r12 .W32)) (.imm (.int64 1)))),
  .label "LBB1_2",
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rdi .W64)) (.regOrMem (.reg (.low .r14 .W64))))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rsi .W64)) (.regOrMem (.reg (.low .r15 .W64))))),
  .instr (.regular .W64 .W64 (.call (.rel (.sub (.label "_swap") .after_current_instruction)))),
  .instr (.regular .W64 .W64 (.dec (.reg (.low .rbx .W64)))),
  .instr (.regular .W64 .W64 (.add (.reg (.low .r15 .W64)) (.imm (.int64 (-8))))),
  .instr (.regular .W64 .W64 (.add (.reg (.low .r14 .W64)) (.imm (.int64 8)))),
  .instr (.regular .W64 .W64 (.cmp (.reg (.low .r12 .W64)) (.regOrMem (.reg (.low .rbx .W64))))),
  .instr (.regular .W64 .W64 (.lea (.low .r12 .W64) ⟨some (.reg .r12), none, .int64 1⟩)),
  .instr (.regular .W64 .W64 (.jcc .c "LBB1_2")),
  .instr (.regular .W64 .W64 (.add (.reg (.low .rsp .W64)) (.imm (.int64 8)))),
  .instr (.regular .W64 .W64 (.pop (.reg (.low .rbx .W64)))),
  .instr (.regular .W64 .W64 (.pop (.reg (.low .r12 .W64)))),
  .instr (.regular .W64 .W64 (.pop (.reg (.low .r14 .W64)))),
  .instr (.regular .W64 .W64 (.pop (.reg (.low .r15 .W64)))),
  .label "LBB1_4",
  .instr (.regular .W64 .W64 .ret)]

attribute [local vcgen_simp] reverse

distill_def reverseInstr [Host] [FunDecls] [Embeds reverse] (g : Fragment)
    (hg : FunDecls.at (label "_swap") = some g)
    (k : BitVec 64 → Int64 → BlockM MachineData Unit)
    (hk : ∀ (r : BitVec 64) (ra : Int64),
      ⦃fun s => s.regs.get64 .rsp = r ∧ s.retAddr = some ra⦄ g.prog ⪯[ofStateRepr abs] (k r ra)
        ⦃fun _ _ => ⊤; AddrRel r ra⦄)
    (r₀ : BitVec 64) (ra : Int64) : BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ reverse ⪯[ofStateRepr abs] reverseInstr
    ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  distill [refines_cfg (p := reverse) (habs := abs_regs), wrp_call hg _ _ hk]
    with finish

end Distillery.Kraken
