import Demo.CfgRewrite
import Demo.InstrCall
import Distillery.Tactic.VCGen.Command

/-!
# `X64Calls`: calls to one callee

The concrete program `calls n` is one block of `n` instructions `callq _swap` followed by `retq`.
The callee is abstract: the run takes the declaration `hg` of `_swap` and the refinement `hk` of its
body to an abstract program `k`, and the rule `wrp_call` turns each call into `callInstr k`. The
family stresses the call rule, which the run applies `n` times with the same hypotheses. No
`vcgen` case corresponds to this family.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr

namespace DistillBench.X64Calls

def calls : Nat → Program
  | 0 => [.instr (.regular .W64 .W64 .ret)]
  | n+1 =>
    .instr (.regular .W64 .W64 (.call (.rel (.sub (.label "_swap") .after_current_instruction)))) ::
    calls n

attribute [vcgen_simp] calls

end DistillBench.X64Calls
