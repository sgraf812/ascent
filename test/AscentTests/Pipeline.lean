import AscentTests.TypeStrengthen
import AscentTests.WordAbstraction

/-!
# An AutoCorres-style two-phase pipeline

A total, word-valued program in the failure monad is abstracted in two steps: type strengthening
removes the failure layer (`ExceptT Unit (StateT σ Id) ↝ StateT σ Id`), then word abstraction
lifts the result `UInt64 ↝ Int`. The phases compose through `Refinement.comp`, yielding a single
refinement of the abstract integer-state program by the concrete failure-monad word program.
-/

open Std.WP Lean.Order Ascent

/-- Word abstraction on the state monad: identity on assertions, values abstracted by `wordVal`. -/
def wordAbstractionStateT : Concretization (Nat → Prop) (Nat → Prop) EStack⟨⟩ EStack⟨⟩ :=
  Concretization.id (Nat → Prop) EStack⟨⟩

/-- The concrete program: a total word computation typed in the failure monad. -/
def concWord : TS Nat UInt64 :=
  MonadLift.monadLift (pure ((10 : UInt64) + 20) : StateT Nat Id UInt64)

/-- Strengthen then word-abstract: the integer state program abstracts the concrete failure-monad
word program, through the composed concretization. -/
example : ⦃(⊤ : Nat → Prop)⦄ concWord
    ⪯[(typeStrengthen Nat).comp wordAbstractionStateT] (pure ((10 : Int) + 20) : StateT Nat Id Int)
    ⦃(⌜wordVal · = ·⌝)⦄ := by
  unfold concWord
  have hWA : ⦃(⊤ : Nat → Prop)⦄ (pure ((10 : UInt64) + 20) : StateT Nat Id UInt64)
      ⪯[wordAbstractionStateT] (pure ((10 : Int) + 20) : StateT Nat Id Int)
      ⦃(⌜wordVal · = ·⌝)⦄ := .pure_eq ⊤ _ (by decide)
  exact Refinement.comp (fun _ => rfl) hWA (refines_lift _ _)
