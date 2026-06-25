import AscentTests.TypeStrengthen
import AscentTests.WordAbstraction

/-!
# An AutoCorres-style two-phase pipeline

A total, word-valued program in the failure monad is abstracted in two steps: type strengthening
removes the failure layer (`ExceptT Unit (StateT σ Id) ↝ StateT σ Id`), then word abstraction
lifts the result `UInt64 ↝ Int`. The phases compose through `Concretization.comp`, exercised here via
the `Trans` instance, yielding a single correspondence from the abstract integer-state program to
the concrete failure-monad word program.
-/

open Std.Internal.Do Lean.Order Ascent

/-- Word abstraction on the state monad: identity on assertions, values abstracted by `wordVal`. -/
def wordAbstractionStateT : Concretization (Nat → Prop) (Nat → Prop) EPost.Nil EPost.Nil :=
  Concretization.id (Nat → Prop) EPost.Nil

/-- The concrete program: a total word computation typed in the failure monad. -/
def concWord : TS Nat UInt64 :=
  MonadLift.monadLift (pure ((10 : UInt64) + 20) : StateT Nat Id UInt64)

/-- Strengthen then word-abstract: the integer state program abstracts the concrete failure-monad
word program, through the composed concretization. -/
example : Corres ((typeStrengthen Nat).comp wordAbstractionStateT) ⊤ (coupleEq (wordVal ∘ id))
    (pure ((10 : Int) + 20) : StateT Nat Id Int) concWord := by
  unfold concWord
  have hWA : Corres wordAbstractionStateT ⊤ (coupleEq wordVal)
      (pure ((10 : Int) + 20) : StateT Nat Id Int)
      (pure ((10 : UInt64) + 20) : StateT Nat Id UInt64) := by
    apply corres_pure ⊤; decide
  exact corres_comp (corres_lift _) hWA
