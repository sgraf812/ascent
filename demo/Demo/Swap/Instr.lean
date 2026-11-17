import Demo.Instr
import Kraken.X64.Parser
import Kraken.X64.PrettyPrint
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

open Kraken.X64.Parser Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

namespace Distillery.Kraken

def swap : Program := parse("
_swap:
  movq (%rdi), %rax
  movq (%rsi), %rcx
  movq %rcx, (%rdi)
  movq %rax, (%rsi)
  retq
")

attribute [local vcgen_simp] swap

distill_def swapInstr [Host] [FunDecls] [Embeds swap] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ swap ⪯[ofStateRepr abs] swapInstr ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  distill [refines_cfg (p := swap) (habs := abs_regs)] with finish

end Distillery.Kraken
