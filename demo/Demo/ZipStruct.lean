import Demo.CfgRewrite
import Demo.Zip

open Std.WP Lean.Order Ascent Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

namespace Ascent.Kraken

sym_simp_def zipWithAddT [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    BlockM MachineData Unit from zipWithAddA s ra
  using pre [tryCatch_table_get_bind, tryCatch_bind_assoc, tryCatch_pure_bind, tryCatch_pure,
    tryCatch_throw, tryCatch_cfgLoop_bind, tryCatch_movRegSib8_bind, tryCatch_addRegSib8_bind,
    tryCatch_movSib8Reg_bind, tryCatch_incReg_bind, tryCatch_xorReg32Reg32_bind, tryCatch_cmpJcc_bind,
    tryCatch_testJcc_bind, tryCatch_ret_bind]
  post [zipWithAddA, zipWithAdd, cfgLoop_label, cfgLoop_entry, cfgLoop_exit,
    CfgLabel.label_eq_label, CfgLabel.label_eq_exit, CfgLabel.exit_eq_label, CfgLabel.label_eq_entry,
    CfgLabel.entry_eq_label, CfgLabel.entry_eq_exit, CfgLabel.exit_eq_entry, eq_self, pure_bind,
    bind_pure_unit, pure_done_eq, throw_eq_toDone, bind_toDone, condState_toDone, forIn_toDone]

#print zipWithAddT

theorem zipWithAddT.refines [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    ⦃(· = s.push64 ra)⦄ zipWithAdd ⪯[ofStateRepr abs] (zipWithAddT s ra) ⦃fun _ _ => ⊤; RetRel s ra⦄ :=
  zipWithAddT.eq s ra ▸ zipWithAddA.refines s ra

#print axioms zipWithAddT.refines

end Ascent.Kraken
