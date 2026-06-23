import AscentTests.Guard

/-!
# A `while` loop in the `UB` monad

Defined as a least fixpoint via `partial_fixpoint`: a non-terminating loop denotes `none`
(undefined / no guarantee), which is consistent with `wp none = ⊥` — so the weakest precondition
of a loop is sound for total correctness (you must prove termination to prove anything).
-/

open Std.Internal.Do Lean.Order Ascent

-- `UB` is `Option`; re-expose its flat-order CCPO and `MonoBind` so `partial_fixpoint` applies.
instance {α} : PartialOrder (UB α) := inferInstanceAs (PartialOrder (Option α))
instance {α} : CCPO (UB α) := inferInstanceAs (CCPO (Option α))
instance : MonoBind UB := inferInstanceAs (MonoBind Option)

/-- `while cond do body`, in `StateT σ UB`. -/
def whileLoop {σ : Type} (cond : σ → Bool) (body : StateT σ UB Unit) : StateT σ UB Unit :=
  fun s => if cond s then body s >>= fun p => whileLoop cond body p.2 else pure ((), s)
partial_fixpoint
