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
abstract machine runs under `JRel (Mem.SubSlots P)`, and the call of `_swap` becomes `callA`.
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
    (hk : ∀ (P' : DataMem) (r₀ : BitVec 64) (ra : Int64),
      (P'.loadInt r₀ 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some ra →
      ⦃fun s => s.regs.get64 .rsp = r₀⦄ g.prog ⪯[ofStateRel (JRel (Mem.SubSlots P'))] (k r₀ 0)
        ⦃fun _ _ => ⊤; RetExit r₀ ra 0⦄)
    (P : DataMem) (r₀ : BitVec 64) (ra L : Int64)
    (hP : (P.loadInt r₀ 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some ra) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀⦄ reverse ⪯[ofStateRel (JRel (Mem.SubSlots P))] reverseA
    ⦃fun _ _ => ⊤; RetExit r₀ ra L⦄
  ascend [refines_cfg_exit (JRel (Mem.SubSlots P)) (fun _ _ h => JRel.regs h) (RetExit r₀ ra L)
    (fun _ _ _ h hs => retExit_stay h hs) (p := reverse), wrp_ret_slots hP, wrp_ret_slots_cons hP,
    wrp_call_slots hg _ _ 0 hk]
    with finish

end Ascent.Kraken
