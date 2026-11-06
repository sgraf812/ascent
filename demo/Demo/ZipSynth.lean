import Demo.ZipS

/-!
# The structured loop, synthesized

`simp_def` is the simplification between the first layer and the next: it unfolds the fused branch
steps and groups each block so that its final branch is on top. `ascend_def` then turns the block
loop into `rotated`, the `if` and `repeat'` form, by `refines_cfgLoop_rotated`, whose side conditions
are found as instances.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

set_option experimental.vcgen true

namespace Ascent.Kraken

attribute [local vcgen_simp] zipWithAdd

simp_def zipWithAddN [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    BlockM MachineData Unit from zipWithAddA s ra
  using [zipWithAddA, bind_pure_unit, Ascent.bind_seq_assoc]

ascend_def zipWithAddS' [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃(⊤ : MachineData → Prop)⦄ (zipWithAddN s ra) ⪯[ofStateRepr id] zipWithAddS'
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [refines_cfgLoop_rotated] with finish


end Ascent.Kraken
