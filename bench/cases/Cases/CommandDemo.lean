import Cases.WordAbs
import Ascend

/-!
# The `ascend` command, end to end

Synthesize the abstract program for `chainC 7 3` directly into a definition, with its certified
refinement theorem, and confirm the synthesized program is the hand-written expected image.
-/

open Std.Internal.Do Lean.Order Ascent AscendBench

ascend_def chainA3 from
  ⦃(⊤ : Prop)⦄ (_ : UB Int) ⊑[γw] (chainC 7 3) ⦃(⌜· = wordVal ·⌝)⦄
  unfolding [chainC]
  by simp only [wordVal, ofProp_prop_eq, UInt64.toNat_add] at * <;> omega

/-- The command produced a refinement theorem against the synthesized constant. -/
example : RTriple chainA3 (chainC 7 3) γw ⊤ (fun a c => ⌜a = wordVal c⌝) ⊥ := chainA3.refines

/-- The synthesized program is definitionally the hand-written image. -/
example : chainA3 = chainA 7 3 := rfl
