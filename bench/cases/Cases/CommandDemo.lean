import Cases.WordAbs
import Ascend

/-!
# The `ascend` command, end to end

Synthesize the abstract program for a concrete program directly into a definition, with its
certified refinement theorem, and confirm the synthesized program is the hand-written expected
image. The concrete program's head definition is unfolded automatically.
-/

open Std.Internal.Do Lean.Order Ascent AscendBench

ascend_def chainA3 from
  ⦃(⊤ : Prop)⦄ (_ : UB Int) ⊑[γw] (chainC 7 3) ⦃(⌜· = wordVal ·⌝)⦄
  by simp only [wordVal, UInt64.toNat_add] at * <;> omega

/-- The command produced a refinement theorem against the synthesized constant. -/
example : RTriple chainA3 (chainC 7 3) γw ⊤ (fun a c => ⌜a = wordVal c⌝) ⊥ := chainA3.refines

/-- The synthesized program is definitionally the hand-written image. -/
example : chainA3 = chainA 7 3 := rfl

/-- A natural right-nested `do`-block: each addition reads the immediately preceding output. The
engine threads the coupled value through the continuation lexically, so the synthesized program
is a chain of guarded sums with no residual holes. -/
def prog : Id UInt64 := do let a ← pure (7 : UInt64); let b ← pure (a + 7); pure (b + 7)

ascend_def progA from
  ⦃(⊤ : Prop)⦄ (_ : UB Int) ⊑[γw] prog ⦃(⌜· = wordVal ·⌝)⦄
  by simp only [wordVal, UInt64.toNat_add] at * <;> omega

/-- The `do`-block abstracts to the guarded chain, threading each output into the next guard. -/
example : progA = (do
    let a ← pure (wordVal 7)
    let b ← UB.guardRet (a + wordVal 7 < 2 ^ 64) (a + wordVal 7)
    UB.guardRet (b + wordVal 7 < 2 ^ 64) (b + wordVal 7)) := rfl
