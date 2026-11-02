import AscentTests.AscendUnfold
import Ascent.Tactic.VCGen.Command

/-!
# The `ascend_def` command

Each command synthesizes an abstract program into a definition, together with its refinement
theorem. A check by `rfl` compares the definition with the expected program.
-/

open Std.WP Lean.Order Ascent WordAbsEngine AscendUnfold

namespace AscendDef

ascend_def chainA3 : UB Int from ⦃(⊤ : Prop)⦄ (chainC 7 3) ⪯[γw] chainA3 ⦃(⌜FunRel wordVal · ·⌝)⦄

example : ⦃(⊤ : Prop)⦄ (chainC 7 3) ⪯[γw] chainA3 ⦃(⌜FunRel wordVal · ·⌝)⦄ := chainA3.refines

example : chainA3 = chainA 7 3 := rfl

/-- Each addition reads the output of the previous one. -/
def prog : Id UInt64 := do let a ← pure (7 : UInt64); let b ← pure (a + 7); pure (b + 7)

ascend_def progA : UB Int from ⦃(⊤ : Prop)⦄ prog ⪯[γw] progA ⦃(⌜FunRel wordVal · ·⌝)⦄

example : progA = (do
    let a ← UB.guardRet True (wordVal 7)
    let b ← UB.guardRet (a + wordVal 7 < 2 ^ 64) (a + wordVal 7)
    UB.guardRet (b + wordVal 7 < 2 ^ 64) (b + wordVal 7)) := rfl

end AscendDef
