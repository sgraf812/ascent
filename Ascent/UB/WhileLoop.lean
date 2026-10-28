import Ascent.UB

/-!
# A `while` loop in the `UB` monad

Defined as a least fixpoint via `partial_fixpoint`: a non-terminating loop denotes `none`
(undefined / no guarantee), which is consistent with `wp none = ⊥`, so the weakest precondition of
a loop is sound for total correctness (you must prove termination to prove anything).
-/

open Std.WP Lean.Order Ascent

-- `UB` is `Option`; re-expose its flat-order CCPO and `MonoBind` so `partial_fixpoint` applies.
instance {α} : PartialOrder (UB α) := inferInstanceAs (PartialOrder (Option α))
instance {α} : CCPO (UB α) := inferInstanceAs (CCPO (Option α))
instance : MonoBind UB := inferInstanceAs (MonoBind Option)

/-- The loop's least fixpoint. `partial_fixpoint` builds it over the *unfolded* state-passing type
`σ → UB (Unit × σ)` (that carries the `CCPO`), so this constant's type is not syntactically `StateT`. -/
def loopFix {σ : Type} (cond : σ → Bool) (body : StateT σ UB Unit) : StateT σ UB Unit :=
  fun s => if cond s then body s >>= fun p => loopFix cond body p.2 else pure ((), s)
partial_fixpoint

/-- `while cond do body`, in `StateT σ UB`. A wrapper whose declared type is `StateT`, so the `WP`
instance fires when taking the loop's `wp` (the bare `loopFix` has the unfolded type). -/
def whileLoop {σ : Type} (cond : σ → Bool) (body : StateT σ UB Unit) : StateT σ UB Unit :=
  loopFix cond body
