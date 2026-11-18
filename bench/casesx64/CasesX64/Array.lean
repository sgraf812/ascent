import Demo.CfgRewrite
import Distillery.Tactic.VCGen.Command

/-!
# `X64Array`: loads and stores at distinct indices

The concrete program `copy n` is one block that copies `n` words: for each `i < n`, the pair
`movq 8i(%rdi), %rax; movq %rax, 8i(%rsi)` loads the word at index `i` of the array at `rdi` and
stores it at index `i` of the array at `rsi`. The Instr step turns each instruction into a memory
access with a guard on the accessed cell. The family stresses the address arithmetic and the guards
of `n` loads and `n` stores. No `vcgen` case corresponds to this family.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr

namespace DistillBench.X64Array

def copyFrom (i : Nat) : Nat → Program
  | 0 => [.instr (.regular .W64 .W64 .ret)]
  | n+1 =>
    .instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64))
      (.regOrMem (.mem ⟨some (.reg .rdi), none, .int64 (Int64.ofNat (8 * i))⟩)))) ::
    .instr (.regular .W64 .W64 (.mov (.mem ⟨some (.reg .rsi), none, .int64 (Int64.ofNat (8 * i))⟩)
      (.regOrMem (.reg (.low .rax .W64))))) ::
    copyFrom (i + 1) n

def copy (n : Nat) : Program := copyFrom 0 n

attribute [vcgen_simp] copyFrom copy

end DistillBench.X64Array
