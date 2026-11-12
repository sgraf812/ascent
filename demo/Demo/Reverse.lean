import Demo.L1Rel
import Demo.L1Gen
import Demo.Swap

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

with `-O1 -fno-vectorize -fno-unroll-loops -fno-builtin -fomit-frame-pointer`. Its refinement to the
abstract machine runs under `JRel Mem.Sub`, and the call of `_swap` becomes `withRa`.
-/

open Kraken.X64.Parser Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRel)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken

def reverse : Program := parse("
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
")

attribute [local vcgen_simp] reverse

ascend_def reverseA [Host] [FunDecls] [Embeds reverse] (g : Fragment)
    (hg : FunDecls.at (label "_swap") = some g)
    (k : BitVec 64 → Int64 → BlockM MachineData Unit)
    (hk : ∀ r₀ ra, ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ g.prog
      ⪯[ofStateRel (JRel Mem.Sub)] (k r₀ ra) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄)
    (r₀ : BitVec 64) (ra : Int64) : BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ reverse ⪯[ofStateRel (JRel Mem.Sub)] reverseA
    ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  ascend [refines_cfg_rel (JRel Mem.Sub) (fun _ _ h => JRel.regs h) (p := reverse),
    wrp_call_withRa hg _ _ hk]
    with finish



end Ascent.Kraken
