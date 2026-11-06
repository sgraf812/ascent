import Demo.Lift

/-!
# `zipWithAdd` with its registers lifted

`zipWithAddL` is `zipWithAddT` over the data memory alone, synthesized by `ascend`. The lifting
relation names the registers that become values: `rdi`, `rsi`, `rdx`, `rcx` and `rsp` are
parameters, and `rax` is the value of the loop. The run binds the loaded values of `r8` as
variables and keeps the guards of the first layer: a load needs a mapped cell, a store also needs
the cell apart from the return slot at `rsp`, and the return needs a mapped return slot.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def zipWithAddL [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)
    (rdi rsi rdx rcx rsp : BitVec 64) : BlockM DataMem Unit from
  ⦃fun t => t.regs.get64 .rdi ≐ rdi ∧ t.regs.get64 .rsi ≐ rsi ∧ t.regs.get64 .rdx ≐ rdx ∧
    t.regs.get64 .rcx ≐ rcx ∧ t.regs.get64 .rsp ≐ rsp⦄
  (zipWithAddT s ra) ⪯[ofStateRepr MachineData.dmem] zipWithAddL
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_forIn_lockstep_unit (R := fun t rax => t.regs.get64 .rdi ≐ rdi ∧
    t.regs.get64 .rsi ≐ rsi ∧ t.regs.get64 .rdx ≐ rdx ∧ t.regs.get64 .rcx ≐ rcx ∧
    t.regs.get64 .rsp ≐ rsp ∧ t.regs.get64 .rax ≐ rax)]

end Ascent.Kraken
