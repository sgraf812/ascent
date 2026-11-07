import Demo.CfgRewrite
import Demo.Zip

/-!
# The structured program of `zipWithAdd`

`zipWithAddT` is the block loop `zipWithAddA` rewritten by the equations of `Demo.CfgRewrite`: the
entry test is a `condState`, the loop block a `repeat'` loop that continues on its jump to itself
and leaves it by the return. `zipWithAddT.refines` is the refinement of `zipWithAddA`,
rewritten along `zipWithAddT.eq`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

namespace Ascent.Kraken

sym_simp_def zipWithAddT [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    BlockM MachineData Unit from zipWithAddA s ra
  using pre [tryCatch_table_get_bind, tryCatch_bind_assoc, tryCatch_pure,
    tryCatch_cfgLoop_bind, tryCatch_modifyIf_bind, tryCatch_branch_bind,
    tryCatch_exitIf_bind, tryCatch_exitIf]
  post [zipWithAddA, zipWithAdd, cfgLoop_exit, cfgLoop_eq_repeat,
    CfgLabel.label_eq_label, bind_pure_unit, pure_bind, AInstr.exitIf_bind, pure_done_eq, bind_map,
    map_exitIf, condState_map, condState_exitIf_map, condState_map_exitIf, forIn_map_done, forIn_exitIf]

theorem zipWithAddT.refines [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    ⦃(· = s.push64 ra)⦄ zipWithAdd ⪯[ofStateRepr abs] (zipWithAddT s ra) ⦃fun _ _ => ⊤; RetRel s ra⦄ :=
  zipWithAddT.eq s ra ▸ zipWithAddA.refines s ra


end Ascent.Kraken
