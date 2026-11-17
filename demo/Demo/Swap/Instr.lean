import Demo.Instr
import Distillery.Tactic.VCGen.Command

/-!
# `swap`

The callee of the function-call example. The x64 text that clang emits for

```c
__attribute__((noinline)) void swap(long *p, long *q) { long t = *p; *p = *q; *q = t; }
```

with `-O1 -fno-vectorize -fno-unroll-loops -fno-builtin -fomit-frame-pointer`, and its refinement to
the abstract machine. The text starts with the label `_swap` that its callers jump to.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

namespace Distillery.Kraken

/-
_swap:
  movq (%rdi), %rax
  movq (%rsi), %rcx
  movq %rcx, (%rdi)
  movq %rax, (%rsi)
  retq
-/
def swap : Program := [
  .label "_swap",
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.regOrMem (.mem ⟨some (.reg .rdi), none, .int64 0⟩)))),
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rcx .W64)) (.regOrMem (.mem ⟨some (.reg .rsi), none, .int64 0⟩)))),
  .instr (.regular .W64 .W64 (.mov (.mem ⟨some (.reg .rdi), none, .int64 0⟩) (.regOrMem (.reg (.low .rcx .W64))))),
  .instr (.regular .W64 .W64 (.mov (.mem ⟨some (.reg .rsi), none, .int64 0⟩) (.regOrMem (.reg (.low .rax .W64))))),
  .instr (.regular .W64 .W64 .ret)]

attribute [local vcgen_simp] swap

distill_def swapInstr [Host] [FunDecls] [Embeds swap] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ swap ⪯[ofStateRepr abs] swapInstr ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  distill [refines_cfg (p := swap) (habs := abs_regs)] with finish

end Distillery.Kraken
