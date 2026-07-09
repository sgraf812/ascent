import Ascent.Corres.Basic

/-!
# `sim`: the relational weakest precondition

`sim γ a c Q E` is the weakest concrete-state precondition under which the abstract program `a`
simulates the concrete program `c`: `Q : AVal → CVal → CPred` couples returned values and `E`
couples thrown values, mirroring `wp x Q E`. `E`'s type is assigned by `HasEPost` from the pair
of barrel shapes: aligned exception layers get `εa → εc → CPred` and the barrel is built by
reifying `E` through `pred` (the exceptional mirror of `Concretization.post`); shapes with
nothing to couple get `Unit` and the barrel is `γ.ePred` (fills are phase data).

The four laws are exactly symmetric: `sim_pure` consumes `Q` and `sim_throw` consumes `E`;
`sim_bind` rebinds `Q` with the continuations' `sim` and `sim_tryCatch` rebinds `E` with the
handlers' (`throw`/`tryCatch` per effect, here for `Except`). A correspondence is the
triple-shaped entailment `pre ⊑ sim γ a c Q E` (`corres_iff_le_sim`, on shapes where the
barrel transport is `γ.ePred`).

`esim γ` is the exception coupling induced by the concretization: the weakest relation on
thrown values under which the abstract barrel concretizes to the concrete one.
-/

open Std.Internal.Do Lean.Order

namespace Ascent

universe u v w w'

/-- Assigns to a pair of barrel shapes the type of the relational exceptional postcondition,
and its concretization against the abstract barrel. -/
class HasEPost (CPred : Type w) (APred : Type w) (CEPred : Type w') (AEPred : Type w')
    (Ξ : outParam (Type u))
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred] where
  /-- The exceptional mirror of `post`. -/
  ePost : Concretization CPred APred CEPred AEPred → Ξ → AEPred → CEPred

instance {CPred APred : Type w} [Assertion CPred] [Assertion APred] :
    HasEPost CPred APred EPost.Nil EPost.Nil Unit where
  ePost γ _ := γ.ePred

/-- A concrete-only barrel couples nothing: the fill is phase data, living in `ePred`. -/
instance {CPred APred εc CRest : Type} [Assertion CPred] [Assertion APred] [Assertion CRest] :
    HasEPost CPred APred (EPost.Cons (εc → CPred) CRest) EPost.Nil Unit where
  ePost γ _ := γ.ePred

/-- Aligned exception layers: the relational head is `post` at the exception values; deeper
layers are concretized by `ePred`. -/
noncomputable instance {CPred APred : Type w} {εa εc : Type u} {ARest CRest : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion ARest] [Assertion CRest] :
    HasEPost CPred APred (EPost.Cons (εc → CPred) CRest) (EPost.Cons (εa → APred) ARest)
      (εa → εc → CPred) where
  ePost γ E Ea := ⟨γ.post E Ea.head, (γ.ePred Ea).tail⟩

/-- The exceptional postcondition concretization: reify the relational exceptional
postcondition against the abstract barrel. The exceptional mirror of `post`. -/
noncomputable def Concretization.ePost {CPred APred : Type w} {CEPred AEPred : Type w'}
    {Ξ : Type u}
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
    [HasEPost CPred APred CEPred AEPred Ξ]
    (γ : Concretization CPred APred CEPred AEPred) (E : Ξ) (Ea : AEPred) : CEPred :=
  HasEPost.ePost γ E Ea

@[simp] theorem Concretization.ePost_nil {CPred APred : Type w}
    [Assertion CPred] [Assertion APred]
    (γ : Concretization CPred APred EPost.Nil EPost.Nil) (E : Unit) (Ea : EPost.Nil) :
    γ.ePost E Ea = γ.ePred Ea := rfl

@[simp] theorem Concretization.ePost_fill {CPred APred εc CRest : Type}
    [Assertion CPred] [Assertion APred] [Assertion CRest]
    (γ : Concretization CPred APred (EPost.Cons (εc → CPred) CRest) EPost.Nil)
    (E : Unit) (Ea : EPost.Nil) :
    γ.ePost E Ea = γ.ePred Ea := rfl

@[simp] theorem Concretization.ePost_cons_head {CPred APred : Type w} {εa εc : Type u}
    {ARest CRest : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion ARest] [Assertion CRest]
    (γ : Concretization CPred APred (EPost.Cons (εc → CPred) CRest)
      (EPost.Cons (εa → APred) ARest))
    (E : εa → εc → CPred) (Ea : EPost.Cons (εa → APred) ARest) :
    (γ.ePost E Ea).head = γ.post E Ea.head := rfl

@[simp] theorem Concretization.ePost_cons_tail {CPred APred : Type w} {εa εc : Type u}
    {ARest CRest : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion ARest] [Assertion CRest]
    (γ : Concretization CPred APred (EPost.Cons (εc → CPred) CRest)
      (EPost.Cons (εa → APred) ARest))
    (E : εa → εc → CPred) (Ea : EPost.Cons (εa → APred) ARest) :
    (γ.ePost E Ea).tail = (γ.ePred Ea).tail := rfl

section
variable {CProg AProg : Type _} {CVal AVal : Type _}
  {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WP CProg CVal CPred CEPred] [WP AProg AVal APred AEPred]
  [HasEPost CPred APred CEPred AEPred Ξ]

/-- The relational weakest precondition: the weakest concrete-state predicate under which every
abstract `wp` fact concretizes to the concrete `wp` at the coupled postconditions. -/
noncomputable def sim (γ : Concretization CPred APred CEPred AEPred)
    (a : AProg) (c : CProg) (Q : AVal → CVal → CPred) (E : Ξ) : CPred :=
  iInf fun Qa : AVal → APred => iInf fun Ea : AEPred =>
    γ.pred (wp a Qa Ea) ⇨ wp c (γ.post Q Qa) (γ.ePost E Ea)

/-- The simulation triple: under precondition `P`, the abstract program `a` approximates the
concrete program `c` through `γ`, with value coupling `Q` and exception coupling `E`. -/
def SimTriple (γ : Concretization CPred APred CEPred AEPred) (P : CPred)
    (a : AProg) (c : CProg) (Q : AVal → CVal → CPred) (E : Ξ) : Prop :=
  P ⊑ sim γ a c Q E

@[inherit_doc SimTriple]
scoped syntax:lead atomic("⦃ " term " ⦄ " term:max " ⊑[") term "] " term:max
  " ⦃ " term "; " term " ⦄" : term

scoped macro_rules
  | `(⦃ $P ⦄ $a ⊑[$γ] $c ⦃ $Q; $E ⦄) => `(SimTriple $γ $P $a $c $Q $E)

/-- Weaken the precondition. -/
theorem SimTriple.weaken {γ : Concretization CPred APred CEPred AEPred} {P' P : CPred}
    {a : AProg} {c : CProg} {Q : AVal → CVal → CPred} {E : Ξ}
    (h : ⦃P⦄ a ⊑[γ] c ⦃Q; E⦄) (hP : P' ⊑ P) : ⦃P'⦄ a ⊑[γ] c ⦃Q; E⦄ :=
  PartialOrder.rel_trans hP h

/-- `sim` is monotone in the value coupling. -/
theorem sim_mono_post [Frame CPred] {γ : Concretization CPred APred CEPred AEPred}
    {a : AProg} {c : CProg} {Q Q' : AVal → CVal → CPred} {E : Ξ}
    (hQ : ∀ av cv, Q av cv ⊑ Q' av cv) : sim γ a c Q E ⊑ sim γ a c Q' E := by
  refine CompleteLattice.iInf_mono fun Qa => CompleteLattice.iInf_mono fun Ea => ?_
  refine CompleteLattice.himp_mono PartialOrder.rel_refl ?_
  refine WP.wp_consequence c _ _ _ ?_
  intro cv
  refine iSup_le _ _ fun av => ?_
  exact PartialOrder.rel_trans
    (le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) (hQ av cv)) (meet_le_right _ _))
    (le_iSup (fun av' => Q' av' cv ⊓ γ.pred (Qa av')) av)

/-- A correspondence entails the relational weakest precondition, on shapes where the barrel
transport is `γ.ePred`. -/
theorem Corres.le_sim {γ : Concretization CPred APred CEPred AEPred}
    {b : Boundary CPred AVal CVal} {a : AProg} {c : CProg} {E : Ξ} (h : Corres γ b a c)
    (hdel : ∀ Ea, γ.ePost E Ea = γ.ePred Ea) :
    b.pre ⊑ sim γ a c b.couple E :=
  le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => by
    rw [hdel Ea]
    exact himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm (h Qa Ea))

/-- The relational weakest precondition is a valid boundary precondition, on shapes where the
barrel transport is `γ.ePred`. -/
theorem corres_sim [Frame CPred] {γ : Concretization CPred APred CEPred AEPred}
    {Q : AVal → CVal → CPred} {E : Ξ} {a : AProg} {c : CProg}
    (hdel : ∀ Ea, γ.ePost E Ea = γ.ePred Ea) :
    Corres γ ⟨sim γ a c Q E, Q⟩ a c := fun Qa Ea => by
  have h := CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea)
      : sim γ a c Q E ⊑ _ ⇨ wp c (γ.post Q Qa) (γ.ePost E Ea))
  rwa [hdel Ea] at h

/-- Any entailment into the relational weakest precondition is a correspondence, on shapes
where the barrel transport is `γ.ePred`. -/
theorem corres_of_le_sim [Frame CPred] {γ : Concretization CPred APred CEPred AEPred}
    {pre : CPred} {Q : AVal → CVal → CPred} {E : Ξ} {a : AProg} {c : CProg}
    (hdel : ∀ Ea, γ.ePost E Ea = γ.ePred Ea)
    (hle : pre ⊑ sim γ a c Q E) : Corres γ ⟨pre, Q⟩ a c := fun Qa Ea =>
  PartialOrder.rel_trans
    (le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) hle) (meet_le_right _ _))
    (corres_sim hdel Qa Ea)

/-- A correspondence is exactly an entailment into the relational weakest precondition, on
shapes where the barrel transport is `γ.ePred`. -/
theorem corres_iff_le_sim [Frame CPred] {γ : Concretization CPred APred CEPred AEPred}
    {pre : CPred} {Q : AVal → CVal → CPred} {E : Ξ} {a : AProg} {c : CProg}
    (hdel : ∀ Ea, γ.ePost E Ea = γ.ePred Ea) :
    Corres γ ⟨pre, Q⟩ a c ↔ pre ⊑ sim γ a c Q E :=
  ⟨fun h => h.le_sim hdel, corres_of_le_sim hdel⟩

end

section
variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WPMonad CM CPred CEPred] [WPMonad AM APred AEPred] [WPMonadExact AM APred AEPred]
  [HasEPost CPred APred CEPred AEPred Ξ]
  {γ : Concretization CPred APred CEPred AEPred}

/-- The relational unit law: `pure` consumes the relational postcondition. -/
theorem sim_pure {AV CV : Type w} {Q : AV → CV → CPred} {E : Ξ} (av : AV) (cv : CV) :
    Q av cv ⊑ sim γ (pure av : AM AV) (pure cv : CM CV) Q E := by
  refine le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => ?_
  refine himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm ?_)
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (γ.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_pure_le av Qa Ea)))) ?_
  exact PartialOrder.rel_trans (le_iSup (fun av' => Q av' cv ⊓ γ.pred (Qa av')) av)
    (WPMonad.pure_le_wp_pure cv (γ.post Q Qa) (γ.ePost E Ea))

/-- The relational bind law: `bind` rebinds the relational postcondition with the
continuations' `sim`; the relational exceptional postcondition threads. -/
theorem sim_bind [Frame CPred] {CV AV CV₂ AV₂ : Type w}
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {Q : AV₂ → CV₂ → CPred} {E : Ξ} :
    sim γ a₁ c₁ (fun av cv => sim γ (a₂ av) (c₂ cv) Q E) E ⊑
      sim γ (a₁ >>= a₂) (c₁ >>= c₂) Q E := by
  refine le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => ?_
  refine himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm ?_)
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (γ.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_bind_le a₁ a₂ Qa Ea)))) ?_
  refine PartialOrder.rel_trans
    (CompleteLattice.meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ (fun av => wp (a₂ av) Qa Ea)) (iInf_le _ Ea))) ?_
  refine PartialOrder.rel_trans
    (WP.wp_consequence c₁ _
      (fun cv => wp (c₂ cv) (γ.post Q Qa) (γ.ePost E Ea))
      (γ.ePost E Ea) ?_)
    (WPMonad.bind_le_wp_bind c₁ c₂ (γ.post Q Qa) (γ.ePost E Ea))
  intro cv
  show iSup (fun av => sim γ (a₂ av) (c₂ cv) Q E ⊓ γ.pred (wp (a₂ av) Qa Ea)) ⊑ _
  refine iSup_le _ _ fun av => ?_
  exact CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))

/-- The triple unit rule: `pure` consumes the value coupling. -/
theorem SimTriple.pure {AV CV : Type w} {Q : AV → CV → CPred} {E : Ξ} (av : AV) (cv : CV) :
    ⦃Q av cv⦄ (pure av : AM AV) ⊑[γ] (pure cv : CM CV) ⦃Q; E⦄ :=
  sim_pure av cv

/-- The triple bind rule, post-parametric form: the head's value coupling is the
continuations' `sim`. -/
theorem SimTriple.bind [Frame CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {Q : AV₂ → CV₂ → CPred} {E : Ξ}
    (h : ⦃P⦄ a₁ ⊑[γ] c₁ ⦃fun av cv => sim γ (a₂ av) (c₂ cv) Q E; E⦄) :
    ⦃P⦄ (a₁ >>= a₂) ⊑[γ] (c₁ >>= c₂) ⦃Q; E⦄ :=
  PartialOrder.rel_trans h sim_bind

/-- The triple bind rule, mid-coupling form: the head establishes `R`, the continuations
correspond under it. -/
theorem SimTriple.bind' [Frame CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {R : AV → CV → CPred} {Q : AV₂ → CV₂ → CPred} {E : Ξ}
    (h₁ : ⦃P⦄ a₁ ⊑[γ] c₁ ⦃R; E⦄)
    (h₂ : ∀ av cv, ⦃R av cv⦄ (a₂ av) ⊑[γ] (c₂ cv) ⦃Q; E⦄) :
    ⦃P⦄ (a₁ >>= a₂) ⊑[γ] (c₁ >>= c₂) ⦃Q; E⦄ :=
  .bind (PartialOrder.rel_trans h₁ (sim_mono_post h₂))

/-- `corres_bind` at the weakest mid-condition: the continuation obligation is `corres_sim`,
leaving the head correspondence and one `wp` fact about the concrete head. -/
theorem corres_bind_pre [Frame CPred] {CV AV CV₂ AV₂ : Type w}
    [WPConjunctive (CM CV) CV CPred CEPred]
    (pre : CPred) (couple : CV → AV) (couple₂ : CV₂ → AV₂) (E : Ξ)
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    (hdel : ∀ Ea, γ.ePost E Ea = γ.ePred Ea)
    (hc : Corres γ (.eq pre couple) a₁ c₁)
    (hmid : pre ⊑
      wp c₁ (fun cv => sim γ (a₂ (couple cv)) (c₂ cv) (coupleEq couple₂) E) ⊥) :
    Corres γ (.eq pre couple₂) (a₁ >>= a₂) (c₁ >>= c₂) :=
  corres_bind pre _ couple couple₂ hc hmid fun _ => corres_sim hdel

/-- The erased-leaf `bind` at the weakest mid-condition. -/
theorem corres_bind_erase_pre [Frame CPred] {CV AV CV₂ AV₂ : Type w}
    [WPConjunctive (CM CV) CV CPred CEPred]
    (pre : CPred) (couple : CV → AV) (couple₂ : CV₂ → AV₂) (E : Ξ)
    {v : AV} {c₁ : CM CV} {a : AM AV₂} {c₂ : CV → CM CV₂}
    (hdel : ∀ Ea, γ.ePost E Ea = γ.ePred Ea)
    (hc : Corres γ (.eq pre couple) (pure v : AM AV) c₁)
    (hmid : pre ⊑ wp c₁ (fun cv => sim γ a (c₂ cv) (coupleEq couple₂) E) ⊥) :
    Corres γ (.eq pre couple₂) a (c₁ >>= c₂) :=
  corres_bind_erase pre _ couple couple₂ hc hmid fun _ => corres_sim hdel

end

section
variable {CPred APred : Type w} {εa εc : Type u} {ARest CRest : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion ARest] [Assertion CRest]

/-- The exception coupling induced by the concretization at a `Cons` layer: the weakest relation
on thrown values under which the abstract barrel concretizes to the concrete one. -/
noncomputable def esim
    (γ : Concretization CPred APred (EPost.Cons (εc → CPred) CRest)
      (EPost.Cons (εa → APred) ARest))
    (ea : εa) (ec : εc) : CPred :=
  iInf fun Ea : EPost.Cons (εa → APred) ARest =>
    γ.pred (Ea.head ea) ⇨ (γ.ePred Ea).head ec

end

section
variable {εa εc AV CV : Type}
  {γ : Concretization Prop Prop (EPost.Cons (εc → Prop) EPost.Nil)
    (EPost.Cons (εa → Prop) EPost.Nil)}

/-- The relational throw law: `throw` consumes the relational exceptional postcondition,
exactly as `pure` consumes the relational postcondition. -/
theorem sim_throw {Q : AV → CV → Prop} {E : εa → εc → Prop} (ea : εa) (ec : εc) :
    E ea ec ⊑
      sim γ (MonadExceptOf.throw ea : Except εa AV)
        (MonadExceptOf.throw ec : Except εc CV) Q E := by
  refine le_iInf _ _ fun Qa => le_iInf _ _ fun Ea => ?_
  refine himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm ?_)
  simp only [WPMonad.wp_throw_Except_apply_eq, Concretization.ePost_cons_head]
  exact CompleteLattice.le_iSup_of_le ea PartialOrder.rel_refl

/-- The relational tryCatch law: `tryCatch` rebinds the relational exceptional postcondition
with the handlers' `sim`, exactly as `bind` rebinds the relational postcondition; the
relational postcondition threads. -/
theorem sim_tryCatch {Q : AV → CV → Prop} {E : εa → εc → Prop}
    {ax : Except εa AV} {cx : Except εc CV}
    {ah : εa → Except εa AV} {ch : εc → Except εc CV} :
    sim γ ax cx Q (fun ea ec => sim γ (ah ea) (ch ec) Q E) ⊑
      sim γ (MonadExceptOf.tryCatch ax ah) (MonadExceptOf.tryCatch cx ch) Q E := by
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
  show iSup (fun ea => sim γ (ah ea) (ch ec) Q E ⊓ γ.pred (wp (ah ea) Qa Ea)) ⊑ _
  refine iSup_le _ _ fun ea => ?_
  exact CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))

end

section
variable {εa εc AV CV : Type}
  {γ : Concretization Prop Prop (EPost.Cons (εc → Prop) EPost.Nil)
    (EPost.Cons (εa → Prop) EPost.Nil)}

/-- The triple throw rule: `throw` consumes the exception coupling. -/
theorem SimTriple.throw {Q : AV → CV → Prop} {E : εa → εc → Prop} (ea : εa) (ec : εc) :
    ⦃E ea ec⦄ (MonadExceptOf.throw ea : Except εa AV)
      ⊑[γ] (MonadExceptOf.throw ec : Except εc CV) ⦃Q; E⦄ :=
  sim_throw ea ec

/-- The triple tryCatch rule, post-parametric form: the body's exception coupling is the
handlers' `sim`. -/
theorem SimTriple.tryCatch {P : Prop} {Q : AV → CV → Prop} {E : εa → εc → Prop}
    {ax : Except εa AV} {cx : Except εc CV}
    {ah : εa → Except εa AV} {ch : εc → Except εc CV}
    (h : ⦃P⦄ ax ⊑[γ] cx ⦃Q; fun ea ec => sim γ (ah ea) (ch ec) Q E⦄) :
    ⦃P⦄ (MonadExceptOf.tryCatch ax ah) ⊑[γ] (MonadExceptOf.tryCatch cx ch) ⦃Q; E⦄ :=
  PartialOrder.rel_trans h sim_tryCatch

end

end Ascent
