import Demo.CfgRewrite
import Distillery.Tactic.VCGen.Command

/-!
# `X64Straight`: a straight-line block of x64 instructions

The concrete program `straight n` is one block of `n` pairs `addq %rbx, %rax; movq %rax, %rcx`
followed by `retq`, on the stub of kraken's x64 machine. The Instr step `refines_cfg` refines the
text to the block loop of the abstract machine, with one abstract step per instruction. The family
stresses the instruction semantics of `Demo.Instr` on a long block, and the `sym_simp_def` step
that structures the block loop. No `vcgen` case corresponds to this family.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr

namespace DistillBench.X64Straight

def straight : Nat → Program
  | 0 => [.instr (.regular .W64 .W64 .ret)]
  | n+1 =>
    .instr (.regular .W64 .W64 (.add (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64))))) ::
    .instr (.regular .W64 .W64 (.mov (.reg (.low .rcx .W64)) (.regOrMem (.reg (.low .rax .W64))))) ::
    straight n

attribute [vcgen_simp] straight

end DistillBench.X64Straight
