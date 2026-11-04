import Demo.AState
import Kraken.X64.Parser
import Ascent.Tactic.VCGen.Frontend

open Kraken.X64.Parser Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true


def loopBody : Program := parse("
  movq (%rsi,%rax,8), %r8
  addq (%rdi,%rax,8), %r8
  movq %r8, (%rdx,%rax,8)
  incq %rax
  cmpq %rax, %rcx
")

noncomputable def loopBodyA [Host] [FunDecls] (t : MachineData) :
    { a : BlockM AState Unit //
      ⦃(· = t)⦄ loopBody ⪯[ofStateRepr abs] a ⦃fun _ _ _ => True; fun _ _ _ => True⦄ } := by
  apply Subtype.mk
  ascend' [loopBody]
