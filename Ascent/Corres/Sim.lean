import Ascent.Corres.Basic

/-!
# `sim`: the relational weakest precondition

`sim r a c Q E` is the weakest concrete-state precondition under which the abstract program `a`
simulates the concrete program `c`: `Q : AVal → CVal → CPred` couples returned values and `E`
couples thrown values, mirroring `wp x Q E`. `E`'s type is assigned by `ECouple` from the pair
of barrel shapes: aligned exception layers get `εa → εc → CPred` and the barrel is built by
reifying `E` through `pred` (the exceptional mirror of `Concretization.post`); shapes with
nothing to couple get `Unit` and the barrel is `r.ePred` (fills are phase data).

The four laws are exactly symmetric: `sim_pure` consumes `Q` and `sim_throw` consumes `E`;
`sim_bind` rebinds `Q` with the continuations' `sim` and `sim_tryCatch` rebinds `E` with the
handlers' (`throw`/`tryCatch` per effect, here for `Except`). A correspondence is the
triple-shaped entailment `pre ⊑ sim r a c Q E` (`corres_iff_le_sim`, on shapes where the
barrel transport is `r.ePred`).

`esim r` is the exception coupling induced by the concretization: the weakest relation on
thrown values under which the abstract barrel concretizes to the concrete one.
-/

open Std.Internal.Do Lean.Order

namespace Ascent

universe u v w w'

/-- Assigns to a pair of barrel shapes the type of the relational exceptional postcondition,
and the barrel transport built from it: coupled layers are reified through `pred`, everything
else is concretized by `ePred`. -/
class ECouple (APred : Type u₁) (CPred : Type u₂) (AEPred : Type u₃) (CEPred : Type u₄)
    (Ξ : outParam (Type u₅)) where
  /-- The barrel transport: the exceptional mirror of `Concretization.post`. -/
  epost : (APred → CPred) → (AEPred → CEPred) → Ξ → AEPred → CEPred

instance {APred : Type u₁} {CPred : Type u₂} :
    ECouple APred CPred EPost.Nil EPost.Nil Unit where
  epost _ ePred _ := ePred

/-- A concrete-only barrel couples nothing: the fill is phase data, living in `ePred`. -/
instance {APred : Type u₁} {CPred : Type u₂} {εc : Type u₄} {CRest : Type u₆} :
    ECouple APred CPred EPost.Nil (EPost.Cons (εc → CPred) CRest) Unit where
  epost _ ePred _ := ePred

/-- Aligned exception layers: the relational head couples thrown values and reifies the
abstract layer through `pred`; deeper layers are concretized by `ePred`. -/
noncomputable instance {APred : Type u₁} {CPred : Type u₂} {εa : Type u₃} {εc : Type u₄}
    {ARest : Type u₅} {CRest : Type u₆} [Assertion CPred] :
    ECouple APred CPred (EPost.Cons (εa → APred) ARest) (EPost.Cons (εc → CPred) CRest)
      (εa → εc → CPred) where
  epost pred ePred E Ea :=
    ⟨fun ec => iSup fun ea => E ea ec ⊓ pred (Ea.head ea), (ePred Ea).tail⟩

/-- The exceptional postcondition concretization: reify the relational exceptional
postcondition against the abstract barrel. The exceptional mirror of `post`. -/
noncomputable def Concretization.epost {CPred APred : Type w} {CEPred AEPred : Type w'}
    {Ξ : Type u}
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
    [ECouple APred CPred AEPred CEPred Ξ]
    (r : Concretization CPred APred CEPred AEPred) (E : Ξ) (Ea : AEPred) : CEPred :=
  ECouple.epost r.pred r.ePred E Ea

@[simp] theorem Concretization.epost_nil {CPred APred : Type w}
    [Assertion CPred] [Assertion APred]
    (r : Concretization CPred APred EPost.Nil EPost.Nil) (E : Unit) (Ea : EPost.Nil) :
    r.epost E Ea = r.ePred Ea := rfl

@[simp] theorem Concretization.epost_fill {CPred APred εc CRest : Type}
    [Assertion CPred] [Assertion APred]
    [Assertion (EPost.Cons (εc → CPred) CRest)]
    (r : Concretization CPred APred (EPost.Cons (εc → CPred) CRest) EPost.Nil)
    (E : Unit) (Ea : EPost.Nil) :
    r.epost E Ea = r.ePred Ea := rfl

@[simp] theorem Concretization.epost_cons_head {CPred APred : Type w} {εa εc : Type u}
    {ARest CRest : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion ARest] [Assertion CRest]
    (r : Concretization CPred APred (EPost.Cons (εc → CPred) CRest)
      (EPost.Cons (εa → APred) ARest))
    (E : εa → εc → CPred) (Ea : EPost.Cons (εa → APred) ARest) (ec : εc) :
    (r.epost E Ea).head ec = iSup fun ea => E ea ec ⊓ r.pred (Ea.head ea) := rfl

@[simp] theorem Concretization.epost_cons_tail {CPred APred : Type w} {εa εc : Type u}
    {ARest CRest : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion ARest] [Assertion CRest]
    (r : Concretization CPred APred (EPost.Cons (εc → CPred) CRest)
      (EPost.Cons (εa → APred) ARest))
    (E : εa → εc → CPred) (Ea : EPost.Cons (εa → APred) ARest) :
    (r.epost E Ea).tail = (r.ePred Ea).tail := rfl

section
variable {CProg AProg : Type _} {CVal AVal : Type _}
  {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WP CProg CVal CPred CEPred] [WP AProg AVal APred AEPred]
  [ECouple APred CPred AEPred CEPred Ξ]

/-- The relational weakest precondition: the weakest concrete-state predicate under which every
abstract `wp` fact concretizes to the concrete `wp` at the coupled postconditions. -/
noncomputable def sim (r : Concretization CPred APred CEPred AEPred)
    (a : AProg) (c : CProg) (Q : AVal → CVal → CPred) (E : Ξ) : CPred :=
  iInf fun Qa : AVal → APred => iInf fun Ea : AEPred =>
    r.pred (wp a Qa Ea) ⇨ wp c (r.post Q Qa) (r.epost E Ea)

/-- A correspondence entails the relational weakest precondition, on shapes where the barrel
transport is `r.ePred`. -/
theorem Corres.le_sim {r : Concretization CPred APred CEPred AEPred}
    {b : Boundary CPred AVal CVal} {a : AProg} {c : CProg} {E : Ξ} (h : Corres r b a c)
    (hdel : ∀ Ea, r.epost E Ea = r.ePred Ea) :
    b.pre ⊑ sim r a c b.couple E :=
  le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => by
    rw [hdel Ea]
    exact himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm (h Qa Ea))

/-- The relational weakest precondition is a valid boundary precondition, on shapes where the
barrel transport is `r.ePred`. -/
theorem corres_sim [Frame CPred] {r : Concretization CPred APred CEPred AEPred}
    {Q : AVal → CVal → CPred} {E : Ξ} {a : AProg} {c : CProg}
    (hdel : ∀ Ea, r.epost E Ea = r.ePred Ea) :
    Corres r ⟨sim r a c Q E, Q⟩ a c := fun Qa Ea => by
  have h := CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea)
      : sim r a c Q E ⊑ _ ⇨ wp c (r.post Q Qa) (r.epost E Ea))
  rwa [hdel Ea] at h

/-- Any entailment into the relational weakest precondition is a correspondence, on shapes
where the barrel transport is `r.ePred`. -/
theorem corres_of_le_sim [Frame CPred] {r : Concretization CPred APred CEPred AEPred}
    {pre : CPred} {Q : AVal → CVal → CPred} {E : Ξ} {a : AProg} {c : CProg}
    (hdel : ∀ Ea, r.epost E Ea = r.ePred Ea)
    (hle : pre ⊑ sim r a c Q E) : Corres r ⟨pre, Q⟩ a c := fun Qa Ea =>
  PartialOrder.rel_trans
    (le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) hle) (meet_le_right _ _))
    (corres_sim hdel Qa Ea)

/-- A correspondence is exactly an entailment into the relational weakest precondition, on
shapes where the barrel transport is `r.ePred`. -/
theorem corres_iff_le_sim [Frame CPred] {r : Concretization CPred APred CEPred AEPred}
    {pre : CPred} {Q : AVal → CVal → CPred} {E : Ξ} {a : AProg} {c : CProg}
    (hdel : ∀ Ea, r.epost E Ea = r.ePred Ea) :
    Corres r ⟨pre, Q⟩ a c ↔ pre ⊑ sim r a c Q E :=
  ⟨fun h => h.le_sim hdel, corres_of_le_sim hdel⟩

end

section
variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WPMonad CM CPred CEPred] [WPMonad AM APred AEPred] [WPMonadExact AM APred AEPred]
  [ECouple APred CPred AEPred CEPred Ξ]
  {r : Concretization CPred APred CEPred AEPred}

/-- The relational unit law: `pure` consumes the relational postcondition. -/
theorem sim_pure {AV CV : Type w} {Q : AV → CV → CPred} {E : Ξ} (av : AV) (cv : CV) :
    Q av cv ⊑ sim r (pure av : AM AV) (pure cv : CM CV) Q E := by
  refine le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => ?_
  refine himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm ?_)
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (r.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_pure_le av Qa Ea)))) ?_
  exact PartialOrder.rel_trans (le_iSup (fun av' => Q av' cv ⊓ r.pred (Qa av')) av)
    (WPMonad.pure_le_wp_pure cv (r.post Q Qa) (r.epost E Ea))

/-- The relational bind law: `bind` rebinds the relational postcondition with the
continuations' `sim`; the relational exceptional postcondition threads. -/
theorem sim_bind [Frame CPred] {CV AV CV₂ AV₂ : Type w}
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {Q : AV₂ → CV₂ → CPred} {E : Ξ} :
    sim r a₁ c₁ (fun av cv => sim r (a₂ av) (c₂ cv) Q E) E ⊑
      sim r (a₁ >>= a₂) (c₁ >>= c₂) Q E := by
  refine le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => ?_
  refine himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm ?_)
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (r.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_bind_le a₁ a₂ Qa Ea)))) ?_
  refine PartialOrder.rel_trans
    (CompleteLattice.meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ (fun av => wp (a₂ av) Qa Ea)) (iInf_le _ Ea))) ?_
  refine PartialOrder.rel_trans
    (WP.wp_consequence c₁ _
      (fun cv => wp (c₂ cv) (r.post Q Qa) (r.epost E Ea))
      (r.epost E Ea) ?_)
    (WPMonad.bind_le_wp_bind c₁ c₂ (r.post Q Qa) (r.epost E Ea))
  intro cv
  show iSup (fun av => sim r (a₂ av) (c₂ cv) Q E ⊓ r.pred (wp (a₂ av) Qa Ea)) ⊑ _
  refine iSup_le _ _ fun av => ?_
  exact CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))

/-- `corres_bind` at the weakest mid-condition: the continuation obligation is `corres_sim`,
leaving the head correspondence and one `wp` fact about the concrete head. -/
theorem corres_bind_pre [Frame CPred] {CV AV CV₂ AV₂ : Type w}
    [WPConjunctive (CM CV) CV CPred CEPred]
    (pre : CPred) (couple : CV → AV) (couple₂ : CV₂ → AV₂) (E : Ξ)
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    (hdel : ∀ Ea, r.epost E Ea = r.ePred Ea)
    (hc : Corres r (.eq pre couple) a₁ c₁)
    (hmid : pre ⊑
      wp c₁ (fun cv => sim r (a₂ (couple cv)) (c₂ cv) (coupleEq couple₂) E) ⊥) :
    Corres r (.eq pre couple₂) (a₁ >>= a₂) (c₁ >>= c₂) :=
  corres_bind pre _ couple couple₂ hc hmid fun _ => corres_sim hdel

/-- The erased-leaf `bind` at the weakest mid-condition. -/
theorem corres_bind_erase_pre [Frame CPred] {CV AV CV₂ AV₂ : Type w}
    [WPConjunctive (CM CV) CV CPred CEPred]
    (pre : CPred) (couple : CV → AV) (couple₂ : CV₂ → AV₂) (E : Ξ)
    {v : AV} {c₁ : CM CV} {a : AM AV₂} {c₂ : CV → CM CV₂}
    (hdel : ∀ Ea, r.epost E Ea = r.ePred Ea)
    (hc : Corres r (.eq pre couple) (pure v : AM AV) c₁)
    (hmid : pre ⊑ wp c₁ (fun cv => sim r a (c₂ cv) (coupleEq couple₂) E) ⊥) :
    Corres r (.eq pre couple₂) a (c₁ >>= c₂) :=
  corres_bind_erase pre _ couple couple₂ hc hmid fun _ => corres_sim hdel

end

section
variable {CPred APred : Type w} {εa εc : Type u} {ARest CRest : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion ARest] [Assertion CRest]

/-- The exception coupling induced by the concretization at a `Cons` layer: the weakest relation
on thrown values under which the abstract barrel concretizes to the concrete one. -/
noncomputable def esim
    (r : Concretization CPred APred (EPost.Cons (εc → CPred) CRest)
      (EPost.Cons (εa → APred) ARest))
    (ea : εa) (ec : εc) : CPred :=
  iInf fun Ea : EPost.Cons (εa → APred) ARest =>
    r.pred (Ea.head ea) ⇨ (r.ePred Ea).head ec

end

section
variable {εa εc AV CV : Type}
  {r : Concretization Prop Prop (EPost.Cons (εc → Prop) EPost.Nil)
    (EPost.Cons (εa → Prop) EPost.Nil)}

/-- The relational throw law: `throw` consumes the relational exceptional postcondition,
exactly as `pure` consumes the relational postcondition. -/
theorem sim_throw {Q : AV → CV → Prop} {E : εa → εc → Prop} (ea : εa) (ec : εc) :
    E ea ec ⊑
      sim r (MonadExceptOf.throw ea : Except εa AV)
        (MonadExceptOf.throw ec : Except εc CV) Q E := by
  refine le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => ?_
  refine himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm ?_)
  simp only [WPMonad.wp_throw_Except_apply_eq, Concretization.epost_cons_head]
  exact CompleteLattice.le_iSup_of_le ea PartialOrder.rel_refl

/-- The relational tryCatch law: `tryCatch` rebinds the relational exceptional postcondition
with the handlers' `sim`, exactly as `bind` rebinds the relational postcondition; the
relational postcondition threads. -/
theorem sim_tryCatch {Q : AV → CV → Prop} {E : εa → εc → Prop}
    {ax : Except εa AV} {cx : Except εc CV}
    {ah : εa → Except εa AV} {ch : εc → Except εc CV} :
    sim r ax cx Q (fun ea ec => sim r (ah ea) (ch ec) Q E) ⊑
      sim r (MonadExceptOf.tryCatch ax ah) (MonadExceptOf.tryCatch cx ch) Q E := by
  refine le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => ?_
  refine himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm ?_)
  simp only [WPMonad.wp_tryCatch_Except_apply_eq]
  refine PartialOrder.rel_trans
    (CompleteLattice.meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ Qa)
        (iInf_le _ (epost⟨fun ea => wp (ah ea) Qa Ea⟩)))) ?_
  refine WP.wp_consequence_econs cx _ _ _ _ PartialOrder.rel_refl ?_
  refine EPost.Cons.mk_le _ _ _ ?_ PartialOrder.rel_refl
  intro ec
  show iSup (fun ea => sim r (ah ea) (ch ec) Q E ⊓ r.pred (wp (ah ea) Qa Ea)) ⊑ _
  refine iSup_le _ _ fun ea => ?_
  exact CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))

end

end Ascent
