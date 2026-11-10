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

sym_simp_def zipWithAddT : BlockM MachineData Unit from zipWithAddA
  using pre [tryCatch_table_get_bind, tryCatch_bind_assoc, tryCatch_pure, BlockLoop.tryCatch_throw,
    tryCatch_modifyIf_bind, tryCatch_branch_bind, tryCatch_peek_bind, tryCatch_exitIf_bind,
    tryCatch_exitIf, tryCatch_condState_bind, tryCatch_condState, tryCatch_map_bind,
    tryCatch_map_condState, tryCatch_map_throw, tryCatch_map_exitIf, tryCatch_map_pure,
    tryCatch_map_modifyIf, BlockLoop.tryCatch_tryCatch, tryCatch_forIn_bind, tryCatch_map_forIn,
    tryCatch_forIn]
  post [zipWithAddA, zipWithAdd, Table.get_cons, Program.table, List.map_cons, List.map_nil,
    jumpTo_none, jumpTo_some, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, cfgLoop_header, cfgLoop_eq_throw,
    ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.map, ThrowsOnly.forIn,
    ThrowsOnly.tryCatch, ThrowsOnly.modifyIf, ThrowsOnly.peek, ThrowsOnly.exitIf,
    ThrowsOnly.branch, ThrowsOnly.condState, ne_eq, not_false_eq_true, and_true, true_and,
    implies_true, forall_const, or_true, true_or, or_false, false_or, CfgLabel.label_eq_label,
    bind_pure_unit, pure_bind, BlockLoop.throw_bind, AInstr.exitIf_bind, pure_done_eq, bind_map,
    condState_map, throw_label_step, map_exitIf, condState_exitIf_map, condState_map_exitIf,
    map_bind_exitIf, condState_bind_exitIf_map, condState_map_bind_exitIf, forIn_map_done,
    forIn_exitIf, forIn_bind_exitIf, forIn_throw, bind_assoc, condState_true, condState_false,
    BitVec.xor_self, BitVec.setWidth_zero]

theorem zipWithAddT.refines [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    ⦃(· = s.push64 ra)⦄ zipWithAdd ⪯[ofStateRepr abs] zipWithAddT ⦃fun _ _ => ⊤; RetRel s ra⦄ :=
  zipWithAddT.eq ▸ zipWithAddA.refines s ra


end Ascent.Kraken
