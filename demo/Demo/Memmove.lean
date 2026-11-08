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

end Ascent.Kraken
