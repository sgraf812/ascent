import Demo.Zip
import Demo.BlockRefine

/-!
# The second layer, smoke test

The identity view: every step refines itself, and the loop refines the loop.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

set_option experimental.vcgen true

namespace Ascent.Kraken

attribute [ascend] wrp_bind wrp_pure_unit

section
variable {Q : Unit → Unit → MachineData → Prop}
  {E : (CfgLabel → CfgLabel → MachineData → Prop) × EStack⟨⟩}

@[ascend] theorem wrp_modifyIf_id (g : MachineData → Prop) (f : MachineData → MachineData) :
    (fun s => g s → Q () () (f s))
      ⊑ wrp (ofStateRepr id) (modifyIf g f) (modifyIf g f) Q E :=
  wrp_modifyIf_repr id g f (fun _ h => h) (fun _ _ => rfl)

@[ascend] theorem wrp_exitIf_id (g : MachineData → Prop) (f : MachineData → MachineData)
    (l : CfgLabel) :
    (fun s => g s → E.1 l l (f s))
      ⊑ wrp (ofStateRepr id) (exitIf g f l) (exitIf g f l) Q E :=
  wrp_exitIf_repr id g f (fun _ h => h) (fun _ _ => rfl) l

@[ascend] theorem wrp_branch_id (c : MachineData → Bool) (l : CfgLabel) :
    (fun s => (c s = true → E.1 l l s) ∧ (c s = false → Q () () s))
      ⊑ wrp (ofStateRepr id) (branch c l) (branch c l) Q E :=
  wrp_branch_repr id c (fun _ => rfl) l

end

ascend_def zipWithAddB [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃(· = s)⦄ (zipWithAddA s ra) ⪯[ofStateRepr id] zipWithAddB
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [zipWithAddA, movRegSib8, addRegSib8, movSib8Reg, incReg, xorReg32Reg32, cmpJcc, testJcc,
    ret, refines_cfgLoop (Concretization.ofStateRepr_pred_iSup id) (I := fun _ => True)]
  with finish

/-- The identity view synthesizes the same program, one `modifyIf` per step. -/
example [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    zipWithAddB s ra = zipWithAddA s ra := rfl

end Ascent.Kraken

