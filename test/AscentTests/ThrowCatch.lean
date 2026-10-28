import Ascent.Refinement
import Ascent.UB

/-!
# Exceptions: the refinement meaning of `throw` and `tryCatch`

`Refinement.throw` consumes the exception relation as `Refinement.pure` consumes the return
relation. `Refinement.tryCatch` rebinds the exception relation with the `wrp` of the handlers as
`Refinement.bind` rebinds the return relation with the `wrp` of the continuations.
-/

open Std.WP Lean.Order Ascent

namespace ThrowCatch

/-- One exception layer (`Nat`-valued exceptions) over pure values. -/
abbrev EE := Nat → Prop

/-- The identity concretization over the exception layer. -/
abbrev exc : Concretization Prop Prop := Concretization.id Prop

/-- `throw` abstracts `throw` at equal codes: the diagonal exception relation is consumed. -/
example {AV CV : Type} (e : Nat) (Q : CV → AV → Prop) :
    ⦃(⊤ : Prop)⦄ (MonadExceptOf.throw e : Except Nat CV)
      ⪯[exc] (MonadExceptOf.throw e : Except Nat AV) ⦃Q; (⌜· = ·⌝)⦄ :=
  (Refinement.throw e e).weaken (CompleteLattice.le_ofProp _ _ rfl)

/-- A `tryCatch` around matching throws runs the handlers: `wrp_throw` consumes the rebound
exception relation at the thrown codes, landing on the handlers' refinement. -/
example {AV CV : Type} {P : Prop} (Q : CV → AV → Prop) (E : Nat → Nat → Prop)
    (ah : Nat → Except Nat AV) (ch : Nat → Except Nat CV)
    (h : ⦃P⦄ (ch 3) ⪯[exc] (ah 3) ⦃Q; E⦄) :
    ⦃P⦄ (MonadExceptOf.tryCatch (MonadExceptOf.throw 3) ch)
      ⪯[exc] (MonadExceptOf.tryCatch (MonadExceptOf.throw 3) ah) ⦃Q; E⦄ :=
  Refinement.tryCatch.weaken (PartialOrder.rel_trans h.le_wrp (Refinement.throw (E := fun ec ea => wrp exc (ch ec) (ah ea) Q E) 3 3).le_wrp)

/-- A caught throw is the handler call: the `throw`/`tryCatch` round trip is erased. -/
theorem refines_catch_throw {AV CV : Type} {P : Prop} {Q : CV → AV → Prop} {E : Nat → Nat → Prop}
    (e : Nat) {a : Except Nat AV} {ch : Nat → Except Nat CV}
    (h : ⦃P⦄ (ch e) ⪯[exc] a ⦃Q; E⦄) :
    ⦃P⦄ (MonadExceptOf.tryCatch (MonadExceptOf.throw e) ch) ⪯[exc] a ⦃Q; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  simp only [WPMonad.wp_tryCatch_Except_apply_eq, WPMonad.wp_throw_Except_apply_eq]
  exact wrp_transport h.le_wrp Qa Ea

/-- Distinct throws admit no refinement under the exception relation `⌜· = ·⌝`. -/
example : ¬ ⦃(⊤ : Prop)⦄ (MonadExceptOf.throw 1 : Except Nat Nat)
    ⪯[exc] (MonadExceptOf.throw 0 : Except Nat Nat) ⦃fun _ _ => ⊤; (⌜· = ·⌝)⦄ := by
  intro hsim
  have H := wrp_transport hsim.le_wrp (fun _ => True) (fun n => n = 0)
  simp only [WPMonad.wp_throw_Except_apply_eq, EPostsConcretization.ePosts_fun,
    Concretization.post_prop, Concretization.id, id_eq, CompleteLattice.ofProp_prop_eq, meet_prop_eq_and,
    top_prop_eq, true_and] at H
  obtain ⟨ea, h1, h0⟩ := H trivial
  omega

end ThrowCatch

namespace RefinementValidation

open Ascent

/-! ## Exception relations between different exception types -/

/-- Throwing errno `3` abstracts to throwing `true` under the code relation, supplied as the
exception relation. -/
example (Q : Int → Int → Prop) :
    ⦃(⊤ : Prop)⦄ (MonadExceptOf.throw 3 : Except Nat Int)
      ⪯[Concretization.id Prop] (MonadExceptOf.throw true : Except Bool Int)
      ⦃Q; fun ec ea => ⌜ea = decide (0 < ec)⌝⦄ :=
  (Refinement.throw 3 true).weaken (CompleteLattice.le_ofProp _ _ (by decide))

/-- A concrete-only exception layer carries a postcondition on the concrete thrown values. `⊤`
permits every concrete throw. -/
example (Q : Int → Int → Prop) :
    ⦃(⊤ : Prop)⦄ (MonadExceptOf.throw 3 : Except Nat Int)
      ⪯[Concretization.id Prop] (pure 0 : Id Int) ⦃Q; fun _ => ⊤⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  simp only [WPMonad.wp_throw_Except_apply_eq, EPostsConcretization.ePosts_fill]
  exact le_top (α := Prop) _

/-- The default exception relation `⊥` forbids every concrete throw. -/
example : ¬ ⦃(⊤ : Prop)⦄ (MonadExceptOf.throw 3 : Except Nat Int)
    ⪯[Concretization.id Prop] (pure 0 : Id Int) ⦃(⌜· = ·⌝)⦄ := by
  intro h
  have h2 := wrp_transport h.le_wrp (fun _ => True) estack⟨⟩
  simp only [WPMonad.wp_throw_Except_apply_eq, EPostsConcretization.ePosts_fill, _root_.top_meet,
    WPMonadExact.wp_pure_eq] at h2
  have hfalse : (⊥ : Nat → Prop) 3 := h2 trivial
  rw [bot_apply, bot_prop_eq] at hfalse
  exact hfalse

end RefinementValidation
