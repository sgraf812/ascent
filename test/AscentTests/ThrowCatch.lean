import Ascent.Corres.RTriple
import Ascent.UB

/-!
# Exceptions: the refinement meaning of `throw` and `tryCatch`

Over one exception layer, `throw` is `pure` into the exception barrel and `tryCatch` is `bind`
on it: `RTriple.throw` consumes the exception coupling exactly as `RTriple.pure` consumes
the value coupling, and `RTriple.tryCatch` rebinds it with the handlers' refinement exactly
as `bind` rebinds the value coupling. A caught throw is the handler call (`refines_catch_throw`),
and inequal throws admit no refinement under the diagonal exception coupling.
-/

open Std.Internal.Do Lean.Order Ascent

namespace ThrowCatch

/-- One exception layer (`Nat`-valued exceptions) over pure values. -/
abbrev EE := EPost.Cons (Nat → Prop) EPost.Nil

/-- The identity concretization over the exception layer. -/
abbrev exc : Concretization Prop Prop EE EE := Concretization.id Prop EE

/-- `throw` abstracts `throw` at equal codes: the diagonal exception coupling is consumed. -/
example {AV CV : Type} (e : Nat) (Q : AV → CV → Prop) :
    ⦃(⊤ : Prop)⦄ (MonadExceptOf.throw e : Except Nat AV)
      ⊑[exc] (MonadExceptOf.throw e : Except Nat CV) ⦃Q; (⌜· = ·⌝)⦄ :=
  (RTriple.throw e e).weaken (le_ofProp _ _ rfl)

/-- A `tryCatch` around matching throws runs the handlers: `rwp_throw` consumes the rebound
exception coupling at the thrown codes, landing on the handlers' refinement. -/
example {AV CV : Type} {P : Prop} (Q : AV → CV → Prop) (E : Nat → Nat → Prop)
    (ah : Nat → Except Nat AV) (ch : Nat → Except Nat CV)
    (h : ⦃P⦄ (ah 3) ⊑[exc] (ch 3) ⦃Q; E⦄) :
    ⦃P⦄ (MonadExceptOf.tryCatch (MonadExceptOf.throw 3) ah)
      ⊑[exc] (MonadExceptOf.tryCatch (MonadExceptOf.throw 3) ch) ⦃Q; E⦄ :=
  RTriple.tryCatch.weaken (PartialOrder.rel_trans h.le_rwp (RTriple.throw (E := fun ea ec => rwp exc (ah ea) (ch ec) Q E) 3 3).le_rwp)

/-- A caught throw is the handler call: the `throw`/`tryCatch` round trip is erased. -/
theorem refines_catch_throw {AV CV : Type} {P : Prop} {Q : AV → CV → Prop} {E : Nat → Nat → Prop}
    (e : Nat) {a : Except Nat AV} {ch : Nat → Except Nat CV}
    (h : ⦃P⦄ a ⊑[exc] (ch e) ⦃Q; E⦄) :
    ⦃P⦄ a ⊑[exc] (MonadExceptOf.tryCatch (MonadExceptOf.throw e) ch) ⦃Q; E⦄ := by
  refine ⟨rwp_intro fun Qa Ea => ?_⟩
  simp only [WPMonad.wp_tryCatch_Except_apply_eq, WPMonad.wp_throw_Except_apply_eq]
  exact rwp_transport h.le_rwp Qa Ea

/-- Distinct throws admit no refinement under the diagonal exception coupling: the barrel
distinguishes the thrown values. -/
example : ¬ ⦃(⊤ : Prop)⦄ (MonadExceptOf.throw 0 : Except Nat Nat)
    ⊑[exc] (MonadExceptOf.throw 1 : Except Nat Nat) ⦃fun _ _ => ⊤; (⌜· = ·⌝)⦄ := by
  intro hsim
  have H := rwp_transport hsim.le_rwp (fun _ => True) (epost⟨fun n => n = 0⟩)
  simp only [WPMonad.wp_throw_Except_apply_eq, Concretization.ePost_cons_head,
    Concretization.post_prop, Concretization.id, id_eq, ofProp_prop_eq, meet_prop_eq_and,
    top_prop_eq, true_and] at H
  obtain ⟨ea, h1, h0⟩ := H trivial
  omega

end ThrowCatch

namespace RTripleValidation

open Ascent

/-! ## Heterogeneous exception couplings: judgment data vs phase data -/

/-- Error-code abstraction: Boolean abstract exceptions over numeric concrete codes; the
concretization carries no exception structure of its own. -/
def errAbs : Concretization Prop Prop (EPost.Cons (Nat → Prop) EPost.Nil)
    (EPost.Cons (Bool → Prop) EPost.Nil) where
  pred := _root_.id
  ePred _ := epost⟨fun _ => ⊥⟩
  pred_mono h := h
  ePred_mono _ := PartialOrder.rel_refl

/-- Throwing errno `3` abstracts to throwing `true` under the code coupling, supplied as the
exception coupling. -/
example (Q : Int → Int → Prop) :
    ⦃(⊤ : Prop)⦄ (MonadExceptOf.throw true : Except Bool Int)
      ⊑[errAbs] (MonadExceptOf.throw 3 : Except Nat Int)
      ⦃Q; fun ea ec => ⌜ea = decide (0 < ec)⌝⦄ :=
  (RTriple.throw true 3).weaken (le_ofProp _ _ (by decide))

/-- Concrete-only exception layer: the fill is phase data. `⊤` permits an unmatched concrete
throw. -/
def fillAbs (fill : Nat → Prop) :
    Concretization Prop Prop (EPost.Cons (Nat → Prop) EPost.Nil) EPost.Nil where
  pred := _root_.id
  ePred _ := epost⟨fill⟩
  pred_mono h := h
  ePred_mono _ := PartialOrder.rel_refl

example (Q : Int → Int → Prop) :
    ⦃(⊤ : Prop)⦄ (pure 0 : Id Int)
      ⊑[fillAbs fun _ => ⊤] (MonadExceptOf.throw 3 : Except Nat Int) ⦃Q⦄ := by
  refine ⟨rwp_intro fun Qa Ea => ?_⟩
  simp only [WPMonad.wp_throw_Except_apply_eq, Concretization.ePost_nil]
  exact le_top _

/-- The `⊥` fill forbids it: type strengthening as `ePred` data. -/
example : ¬ ⦃(⊤ : Prop)⦄ (pure 0 : Id Int)
    ⊑[fillAbs fun _ => ⊥] (MonadExceptOf.throw 3 : Except Nat Int) ⦃(⌜· = ·⌝)⦄ := by
  intro h
  have h2 := rwp_transport h.le_rwp (fun _ => True) EPost.Nil.mk
  simp only [WPMonad.wp_throw_Except_apply_eq, Concretization.ePost_nil, top_meet,
    WPMonadExact.wp_pure_eq] at h2
  have hfalse := h2 trivial
  rw [bot_prop_eq] at hfalse
  exact hfalse

end RTripleValidation
