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

/-! ## `sim`/`esim` validation: induced exception couplings, generation, fills -/

/-- Error-code abstraction: Boolean abstract exceptions over numeric concrete codes, the
`ePred` built by reifying the code coupling `ea = decide (0 < ec)` through `pred`. -/
noncomputable def errAbs : Concretization Prop Prop (EPost.Cons (Nat → Prop) EPost.Nil)
    (EPost.Cons (Bool → Prop) EPost.Nil) where
  pred := _root_.id
  ePred Ea := epost⟨fun ec => iSup fun ea => (⌜ea = decide (0 < ec)⌝ : Prop) ⊓ Ea.head ea⟩
  pred_mono h := h
  ePred_mono {Ea Ea'} h := by
    have h' : Ea.head ⊑ Ea'.head ∧ Ea.tail ⊑ Ea'.tail := by
      simpa [PartialOrder.rel, meet_prop_eq_and] using h
    refine EPost.Cons.mk_le _ _ _ ?_ (EPost.Nil.le _)
    intro ec
    show iSup (fun ea => (⌜ea = decide (0 < ec)⌝ : Prop) ⊓ Ea.head ea) ⊑
      iSup fun ea => (⌜ea = decide (0 < ec)⌝ : Prop) ⊓ Ea'.head ea
    refine iSup_le _ _ fun ea => ?_
    exact PartialOrder.rel_trans
      (le_meet _ _ _ (meet_le_left _ _)
        (PartialOrder.rel_trans (meet_le_right _ _) (h'.1 ea)))
      (le_iSup (fun ea => (⌜ea = decide (0 < ec)⌝ : Prop) ⊓ Ea'.head ea) ea)

/-- Throwing errno `3` abstracts to throwing `true`: the reified kernel lies below the induced
coupling `esim errAbs`, and `sim_throw` consumes it. -/
example (Q : Int → Int → Prop) :
    (⊤ : Prop) ⊑ sim errAbs (MonadExceptOf.throw true : Except Bool Int)
      (MonadExceptOf.throw 3 : Except Nat Int) Q := by
  refine PartialOrder.rel_trans ?_ (sim_throw true 3)
  refine le_iInf _ _ fun Ea => ?_
  refine himp_complete _ _ _ ?_
  refine CompleteLattice.le_iSup_of_le true ?_
  exact le_meet _ _ _ (le_ofProp _ _ (by decide)) (meet_le_left _ _)

/-- The identity concretization satisfies `sim_tryCatch`'s generation hypothesis: `esim` at the
diagonal is `⊤`, so each barrel value generates itself. -/
example {ε : Type} (Ea : EPost.Cons (ε → Prop) EPost.Nil) (ec : ε) :
    ((Concretization.id Prop (EPost.Cons (ε → Prop) EPost.Nil)).ePred Ea).head ec ⊑
      iSup fun ea => esim (Concretization.id Prop (EPost.Cons (ε → Prop) EPost.Nil)) ea ec
        ⊓ (Concretization.id Prop (EPost.Cons (ε → Prop) EPost.Nil)).pred (Ea.head ea) := by
  refine CompleteLattice.le_iSup_of_le ec ?_
  refine le_meet _ _ _ ?_ PartialOrder.rel_refl
  refine PartialOrder.rel_trans (le_top _) ?_
  refine le_iInf _ _ fun Ea' => ?_
  exact himp_complete _ _ _ (meet_le_left _ _)

/-- Concrete-only exception layer with a fill: `⊤` permits an unmatched concrete throw. -/
noncomputable def fillAbs (fill : Nat → Prop) :
    Concretization Prop Prop (EPost.Cons (Nat → Prop) EPost.Nil) EPost.Nil where
  pred := _root_.id
  ePred _ := epost⟨fill⟩
  pred_mono h := h
  ePred_mono _ := PartialOrder.rel_refl

example (Q : Int → Int → Prop) :
    (⊤ : Prop) ⊑ sim (fillAbs fun _ => ⊤) (pure 0 : Id Int)
      (MonadExceptOf.throw 3 : Except Nat Int) Q := by
  refine le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => ?_
  refine himp_complete _ _ _ ?_
  simp only [WPMonad.wp_throw_Except_apply_eq]
  exact le_top _

/-- The `⊥` fill forbids it: type strengthening as `ePred` data. -/
example : ¬ ((⊤ : Prop) ⊑ sim (fillAbs fun _ => ⊥) (pure 0 : Id Int)
      (MonadExceptOf.throw 3 : Except Nat Int) (fun av cv => ⌜av = cv⌝)) := by
  intro h
  have h2 := CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans h
      (PartialOrder.rel_trans (iInf_le _ (fun _ => True)) (iInf_le _ EPost.Nil.mk)))
  simp only [WPMonad.wp_throw_Except_apply_eq, top_meet, WPMonadExact.wp_pure_eq] at h2
  have hfalse := h2 trivial
  rw [bot_prop_eq] at hfalse
  exact hfalse

end SimValidation
