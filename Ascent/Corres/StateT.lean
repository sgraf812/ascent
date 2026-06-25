import Ascent.UB

/-!
# `Corres` over `StateT σ UB`

The facts that make `StateT σ UB` a usable concrete monad for `Corres`: its `wp` reduces `bind`
pointwise, and the conjunctivity class `ConjWP` is inhabited (needed by the precondition-threading
`corres_bind`).
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

/-- `StateT σ UB` has conjunctive `wp` (the lattice form, threaded through the state). -/
instance {σ} : ConjWP (StateT σ UB) (σ → Prop) EPost.Nil where
  wp_meet x A B E := by
    intro s
    simp only [meet_apply, StateT.wp_apply_eq]
    exact UB.wp_meet (x s) (fun p => A p.1 p.2) (fun p => B p.1 p.2) E

