import Demo.L1
import Kraken.X64.Parser
import Ascent.Tactic.VCGen.Command

/-!
# A carried flag across blocks

The loop block of `decLoop` branches on the flag that `decq %rcx` writes. The run binds that flag
to a value of the abstract program and fills the rest of the block under that value, while the
table of blocks is shared with the goal of the next block.
-/

open Kraken.X64.Parser Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken.HoleScope

def decLoop : Program := parse("
LBB0_3:
  decq %rcx
  jne LBB0_3
LBB0_7:
  retq
")

attribute [local vcgen_simp] decLoop

ascend_def decLoopA [Host] [FunDecls] [Embeds decLoop] (s : MachineData) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃(· = s.push64 ra)⦄ decLoop ⪯[ofStateRepr abs] decLoopA ⦃fun _ _ => ⊤; RetRel s ra⦄
  ascend [refines_cfg (p := decLoop)] with finish

end Ascent.Kraken.HoleScope
