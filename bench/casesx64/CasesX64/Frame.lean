import Demo.CfgRewrite
import Distillery.Tactic.VCGen.Command

/-!
# `X64Frame`: pushes and pops

The concrete program `frame n` is one block of `n` instructions `pushq %rbx`, then `n` instructions
`popq %rbx`, then `retq`. Each push stores a word below `rsp` and each pop loads it back, so each
step of the abstract block loop is a memory access whose guard states that the stack cell is mapped.
The family stresses the stack accesses of the Instr step and the `rsp` arithmetic of its rules. No
`vcgen` case corresponds to this family.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr

namespace DistillBench.X64Frame

def pops : Nat → Program
  | 0 => [.instr (.regular .W64 .W64 .ret)]
  | n+1 => .instr (.regular .W64 .W64 (.pop (.reg (.low .rbx .W64)))) :: pops n

def frame : Nat → Nat → Program
  | 0, m => pops m
  | n+1, m => .instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low .rbx .W64))))) :: frame n m

attribute [vcgen_simp] pops frame

end DistillBench.X64Frame
