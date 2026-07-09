import Ascent.Corres.Basic
import Ascent.Corres.Sim
import Ascent.UB

/-!
# Exceptions: the `Corres` meaning of `throw` and `tryCatch`

Over one exception layer with the identity concretization, `throw` is `pure` into the exception
barrel and `tryCatch` is `bind` on it: `corres_throw` needs no value-coupling premise (no value
crosses the boundary; the exception values are coupled diagonally by the identity `ePred`), and
`corres_tryCatch` composes a body correspondence with a handler correspondence per exception,
the body instantiated at the barrel holding the abstract handler's `wp`. A caught throw is the
handler call (`corres_catch_throw`), and inequal throws admit no correspondence.
-/

open Std.Internal.Do Lean.Order Ascent

namespace ThrowCatch

/-- One exception layer (`Nat`-valued exceptions) over pure values. -/
abbrev EE := EPost.Cons (Nat → Prop) EPost.Nil

/-- The identity concretization over the exception layer. -/
abbrev exc : Concretization Prop Prop EE EE := Concretization.id Prop EE

/-- `throw` abstracts `throw`, under any boundary: no value crosses, and the identity `ePred`
couples the exception values diagonally. -/
theorem corres_throw {AV CV : Type} (e : Nat) (b : Boundary Prop AV CV) :
    Corres exc b (throw e : Except Nat AV) (throw e : Except Nat CV) := by
  intro Q E
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  show wp (MonadExceptOf.throw e : Except Nat AV) Q E ⊑
    wp (MonadExceptOf.throw e : Except Nat CV) (exc.post b.couple Q) E
  simp only [WPMonad.wp_throw_Except_apply_eq]
  exact PartialOrder.rel_refl

/-- `tryCatch` abstracts `tryCatch` when the bodies correspond and the handlers correspond
pointwise: `bind` on the exception barrel. -/
theorem corres_tryCatch {AV CV : Type} (couple : CV → AV)
    {ax : Except Nat AV} {cx : Except Nat CV} {ah : Nat → Except Nat AV}
    {ch : Nat → Except Nat CV}
    (hx : Corres exc (.eq ⊤ couple) ax cx)
    (hh : ∀ e, Corres exc (.eq ⊤ couple) (ah e) (ch e)) :
    Corres exc (.eq ⊤ couple) (tryCatch ax ah) (tryCatch cx ch) := by
  intro Q E
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  show wp (MonadExceptOf.tryCatch ax ah) Q E ⊑
    wp (MonadExceptOf.tryCatch cx ch) (exc.post (coupleEq couple) Q) E
  simp only [WPMonad.wp_tryCatch_Except_apply_eq]
  have hbody := hx Q (epost⟨fun e => wp (ah e) Q E⟩)
  refine PartialOrder.rel_trans
    (PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl) hbody) ?_
  refine WP.wp_consequence_econs cx _ _ _ _ PartialOrder.rel_refl ?_
  refine EPost.Cons.mk_le _ _ _ ?_ (EPost.Nil.le _)
  intro e
  exact PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl) (hh e Q E)

/-- A caught throw is the handler call: the `throw`/`tryCatch` round trip is erased. -/
theorem corres_catch_throw {CV : Type} (e : Nat) (ch : Nat → Except Nat CV) :
    Corres exc (.eq ⊤ (id : CV → CV)) (ch e) (tryCatch (throw e) ch) := by
  intro Q E
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  show wp (ch e) Q E ⊑ wp (MonadExceptOf.tryCatch (MonadExceptOf.throw e) ch) (exc.post (coupleEq id) Q) E
  simp only [WPMonad.wp_tryCatch_Except_apply_eq, WPMonad.wp_throw_Except_apply_eq,
    Concretization.post_coupleEq, Concretization.id, id_eq]
  exact PartialOrder.rel_refl

/-- Distinct throws admit no correspondence: the barrel distinguishes the exception values. -/
example : ¬ Corres exc .trivial (throw 0 : Except Nat Nat) (throw 1 : Except Nat Nat) := by
  intro hcorres
  have h : ((0 : Nat) = 0) → ((1 : Nat) = 0) :=
    PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl)
      (hcorres (fun _ => True) (epost⟨fun n => n = 0⟩))
  exact Nat.one_ne_zero (h rfl)

end ThrowCatch

namespace SimValidation

open Ascent

/-! ## `sim` validation: exception-value coupling as judgment data, fills as phase data -/

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
      ⪯[errAbs] (MonadExceptOf.throw 3 : Except Nat Int)
      ⦃Q; fun ea ec => ⌜ea = decide (0 < ec)⌝⦄ :=
  (SimTriple.throw true 3).weaken (le_ofProp _ _ (by decide))

/-- Concrete-only exception layer: the fill is phase data. `⊤` permits an unmatched concrete
throw. -/
def fillAbs (fill : Nat → Prop) :
    Concretization Prop Prop (EPost.Cons (Nat → Prop) EPost.Nil) EPost.Nil where
  pred := _root_.id
  ePred _ := epost⟨fill⟩
  pred_mono h := h
  ePred_mono _ := PartialOrder.rel_refl

example (Q : Int → Int → Prop) :
    (⊤ : Prop) ⊑ sim (fillAbs fun _ => ⊤) (pure 0 : Id Int)
      (MonadExceptOf.throw 3 : Except Nat Int) Q ⟨⟩ := by
  refine le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => ?_
  refine himp_complete _ _ _ ?_
  simp only [WPMonad.wp_throw_Except_apply_eq, Concretization.ePost_fill]
  exact le_top _

/-- The `⊥` fill forbids it: type strengthening as `ePred` data. -/
example : ¬ ((⊤ : Prop) ⊑ sim (fillAbs fun _ => ⊥) (pure 0 : Id Int)
      (MonadExceptOf.throw 3 : Except Nat Int) (fun av cv => ⌜av = cv⌝) ⟨⟩) := by
  intro h
  have h2 := CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans h
      (PartialOrder.rel_trans (iInf_le _ (fun _ => True)) (iInf_le _ EPost.Nil.mk)))
  simp only [WPMonad.wp_throw_Except_apply_eq, Concretization.ePost_fill, top_meet,
    WPMonadExact.wp_pure_eq] at h2
  have hfalse := h2 trivial
  rw [bot_prop_eq] at hfalse
  exact hfalse

end SimValidation
