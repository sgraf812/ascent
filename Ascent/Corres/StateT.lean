import Ascent.UB

/-!
# Refinement over `StateT σ UB`

The facts that make `StateT σ UB` a usable concrete monad for refinement: its `wp` reduces `bind`
pointwise, and conjoins two established postconditions (`wp_and_StateT`). Conjunctivity as the
lattice-form `WPConjunctive` class, needed by `Refines.conj_wp`, is provided for `StateT σ UB`
by the library instances (`StateT.instWPConjunctive` over `UB`'s).
-/

open Std.Internal.Do Lean.Order Ascent

/-- `wp` of a `StateT σ UB` bind, pointwise in the state. -/
theorem wp_bind_StateT {σ α β} (x : StateT σ UB α) (f : α → StateT σ UB β)
    (Q : β → σ → Prop) (E : EPost.Nil) (s : σ) :
    wp (x >>= f) Q E s = wp x (fun a s' => wp (f a) Q E s') E s := by
  simp only [StateT.wp_apply_eq, StateT.run_bind, UB.wp_bind_eq]

/-- `StateT σ UB`'s `wp` conjoins postconditions (the demonic `UB` base is deterministic). -/
theorem wp_and_StateT {σ α} (x : StateT σ UB α) (P R : α → σ → Prop) (E : EPost.Nil) (s : σ)
    (hP : wp x P E s) (hR : wp x R E s) : wp x (fun a s' => P a s' ∧ R a s') E s := by
  rw [StateT.wp_apply_eq] at hP hR ⊢
  exact UB.wp_and (x.run s) (fun p => P p.1 p.2) (fun p => R p.1 p.2) E hP hR


