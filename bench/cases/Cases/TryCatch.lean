import Cases.WordAbs
import Ascend

/-!
# `tryCatch` synthesis, end to end

The exception side is decomposed by the same generic machinery as the value side: `tryCatch`
is a registered structural rule whose body and handler are sub-programs, synthesized as holes
exactly as `bind`'s head and continuation. The concrete program catches a thrown value with an
identity handler; the synthesized abstract program mirrors it under the identity concretization.
-/

open Std.WP Lean.Order Ascent AscendBench

/-- The identity concretization over `Except Nat`, aligning the single exception layer. -/
noncomputable def γe : Concretization Prop Prop EPost⟨Nat → Prop⟩ EPost⟨Nat → Prop⟩ :=
  Concretization.id Prop EPost⟨Nat → Prop⟩

-- A `pure` leaf under the identity concretization, coupling by equality.
attribute [local ascend] Ascent.Refinement.pure

/-- Catch a thrown value and return it: `tryCatch (throw 5) pure` evaluates to `.ok 5`. -/
def ctc : Except Nat Nat :=
  MonadExceptOf.tryCatch (MonadExceptOf.throw 5) (fun e => pure e)

ascend_def atc from
  ⦃(⊤ : Prop)⦄ ctc ⪯[γe] (_ : Except Nat Nat) ⦃(fun c a => ⌜c = a⌝); (fun ec ea => ⌜ec = ea⌝)⦄
  by first | rfl | (intro h; exact h) | simp_all

/-- The command produced a refinement theorem against the synthesized constant. -/
example : Refinement ctc atc γe ⊤ (fun c a => ⌜c = a⌝) (fun ec ea => ⌜ec = ea⌝) :=
  atc.refines

/-- The synthesized program is the identity image of the concrete one. -/
example : atc = MonadExceptOf.tryCatch (MonadExceptOf.throw 5) (fun e => pure e) := rfl
