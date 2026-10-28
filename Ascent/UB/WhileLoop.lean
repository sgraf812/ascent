import Ascent.UB

/-!
# `while` in `StateT σ UB`

`whileLoop cond body` is the least fixpoint of one unfolding of the loop, taken with
`partial_fixpoint` in the flat order of `UB`. A loop that runs forever denotes `none`, so its
`wp` is `⊥`.
-/

open Std.WP Lean.Order Ascent

instance {α} : PartialOrder (UB α) := inferInstanceAs (PartialOrder (Option α))
instance {α} : CCPO (UB α) := inferInstanceAs (CCPO (Option α))
instance : MonoBind UB := inferInstanceAs (MonoBind Option)

/-- The fixpoint, at the state-passing type `σ → UB (Unit × σ)` that carries the `CCPO`. -/
def loopFix {σ : Type} (cond : σ → Bool) (body : StateT σ UB Unit) : StateT σ UB Unit :=
  fun s => if cond s then body s >>= fun p => loopFix cond body p.2 else pure ((), s)
partial_fixpoint

/-- `while cond do body`. The type is `StateT σ UB Unit`, so the `WP` instance of `StateT`
applies. -/
def whileLoop {σ : Type} (cond : σ → Bool) (body : StateT σ UB Unit) : StateT σ UB Unit :=
  loopFix cond body
