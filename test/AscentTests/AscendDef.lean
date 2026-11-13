import AscentTests.AscendUnfold
import Ascent.Tactic.VCGen.Command

/-!
# The `ascend_def` command

Each command synthesizes an abstract program into a definition, together with its refinement
theorem. A check by `rfl` compares the definition with the expected program.
-/

open Std.WP Lean.Order Ascent WordAbsEngine AscendUnfold

namespace AscendDef

ascend_def chainA3 : Demonic Int from ⦃(⊤ : Prop)⦄ (chainC 7 3) ⪯[γw] chainA3 ⦃(⌜FunRel wordVal · ·⌝)⦄
  ascend [chainC]

example : ⦃(⊤ : Prop)⦄ (chainC 7 3) ⪯[γw] chainA3 ⦃(⌜FunRel wordVal · ·⌝)⦄ := chainA3.refines

example : chainA3 = chainA 7 3 := rfl

/-- Each addition reads the output of the previous one. -/
def prog : Id UInt64 := do let a ← pure (7 : UInt64); let b ← pure (a + 7); pure (b + 7)

ascend_def progA : Demonic Int from ⦃(⊤ : Prop)⦄ prog ⪯[γw] progA ⦃(⌜FunRel wordVal · ·⌝)⦄
  ascend [prog]

example : progA = (do
    let a ← (do Demonic.assume True; pure (wordVal 7))
    let b ← (do Demonic.assume (a + wordVal 7 < 2 ^ 64); pure (a + wordVal 7))
    (do Demonic.assume (b + wordVal 7 < 2 ^ 64); pure (b + wordVal 7))) := rfl

sym_simp_def progS : Id UInt64 from prog using pre [] post [prog]

/-- info: [15, 15, 33, 33] -/
#guard_msgs in
#eval show Lean.Elab.Command.CommandElabM (List Nat) from do
  let names := [``chainA3, ``chainA3.refines, ``progS, ``progS.eq]
  names.mapM fun n => return ((← Lean.findDeclarationRanges? n).map (·.range.pos.line)).getD 0

end AscendDef
