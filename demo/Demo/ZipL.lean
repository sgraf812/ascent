import Demo.Lift

/-!
# `zipWithAdd` with its registers lifted

`zipWithAddL₀` is `zipWithAddT` over the data memory alone, synthesized by `ascend`, and
`zipWithAddL` is `zipWithAddL₀` with its branch conditions stated as comparisons of the values. The lifting
relation `RegsRel` names the registers that become values: `rdi`, `rsi`, `rdx`, `rcx` and `rsp` are
parameters, and `rax` is the value of the loop. The run binds the loaded values of `r8` as
variables and keeps the guards of the first layer: a load needs a mapped cell, a store also needs
the cell apart from the return slot at `rsp`, and the return needs a mapped return slot.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def zipWithAddL₀ [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)
    (rdi rsi rdx rcx rsp : BitVec 64) : BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rcx, rcx), (.rsp, rsp)]⦄
  (zipWithAddT s ra) ⪯[ofStateRepr MachineData.dmem] zipWithAddL₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_forIn_lockstep_unit (R := fun t rax =>
    RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rcx, rcx), (.rsp, rsp), (.rax, rax)] t)]

sym_simp_def zipWithAddL [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)
    (rdi rsi rdx rcx rsp : BitVec 64) : BlockM DataMem Unit from zipWithAddL₀ s ra rdi rsi rdx rcx rsp
  using pre [] post [zipWithAddL₀, CondCode.cmp_nz_eq_true, CondCode.cmp_le_eq_true, BitVec.and_self,
    BitVec.toInt_zero, bind_pure_unit, pure_bind]

theorem zipWithAddL.refines [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)
    (rdi rsi rdx rcx rsp : BitVec 64) :
    ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rcx, rcx), (.rsp, rsp)]⦄
      (zipWithAddT s ra) ⪯[ofStateRepr MachineData.dmem] (zipWithAddL s ra rdi rsi rdx rcx rsp)
      ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  zipWithAddL.eq s ra rdi rsi rdx rcx rsp ▸ zipWithAddL₀.refines s ra rdi rsi rdx rcx rsp

end Ascent.Kraken
