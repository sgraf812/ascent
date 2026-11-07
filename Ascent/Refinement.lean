import Ascent.WRP
import Ascent.WPCont

/-!
# Refinement

`Refinement c a γ P Q E` states `P ⊑ wrp γ c a Q E`: under the precondition `P`, the concrete
program `c` refines the abstract program `a`. The notation is `⦃P⦄ c ⪯[γ] a ⦃Q; E⦄`, and
`⦃P⦄ c ⪯[γ] a ⦃Q⦄` sets `E := ⊥`.

`Refinement.transport` turns a Hoare triple `Triple a Pa Qa Ea` about the abstract program into
the Hoare triple `Triple c (P ⊓ γ.pred Pa) (γ.post Q Qa) (ePosts γ E Ea)` about the concrete
program.

The triple forms of the `wrp` laws carry the rebound `wrp` in the precondition, so they apply to
every return relation by instantiation.
-/

open Std.WP Lean.Order

namespace Ascent

universe u v w w'

/-- The refinement triple `P ⊑ wrp γ c a Q E`, written `⦃P⦄ c ⪯[γ] a ⦃Q; E⦄`. -/
structure Refinement {CProg AProg : Type _} {CVal AVal : Type _}
    {CPred APred : Type w} {CEPosts AEPosts : Type w'} {ERels : Type u}
    [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
    (c : CProg) (a : AProg)
    [WP CProg CVal CPred CEPosts] [WP AProg AVal APred AEPosts]
    (γ : Concretization CPred APred)
    [EPostsConcretization CPred APred CEPosts AEPosts ERels]
    (P : CPred) (Q : CVal → AVal → CPred) (E : ERels) : Prop where
  intro ::
  /-- The precondition entails the weakest refinement precondition. -/
  le_wrp : P ⊑ wrp γ c a Q E

/-- The triple without an exception relation. `E` is `⊥`. -/
scoped syntax:lead atomic("⦃ " term " ⦄ " term:max " ⪯[") term "] " term:max
  " ⦃ " term " ⦄" : term

@[inherit_doc Refinement]
scoped syntax:lead atomic("⦃ " term " ⦄ " term:max " ⪯[") term "] " term:max
  " ⦃ " term "; " term " ⦄" : term

scoped macro_rules
  | `(⦃ $P ⦄ $c ⪯[$γ] $a ⦃ $Q ⦄) => `(Refinement $c $a $γ $P $Q Lean.Order.bot)
  | `(⦃ $P ⦄ $c ⪯[$γ] $a ⦃ $Q; $E ⦄) => `(Refinement $c $a $γ $P $Q $E)

section
variable {CProg AProg : Type _} {CVal AVal : Type _}
  {CPred APred : Type w} {CEPosts AEPosts : Type w'} {ERels : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WP CProg CVal CPred CEPosts] [WP AProg AVal APred AEPosts]
  [EPostsConcretization CPred APred CEPosts AEPosts ERels]

variable {γ : Concretization CPred APred} {P : CPred}
  {c : CProg} {a : AProg} {Q : CVal → AVal → CPred} {E : ERels}

theorem Refinement.weaken {P' : CPred}
    (h : ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄) (hP : P' ⊑ P) : ⦃P'⦄ c ⪯[γ] a ⦃Q; E⦄ :=
  ⟨PartialOrder.rel_trans hP h.le_wrp⟩

theorem Refinement.mono_post [Heyting CPred] {Q' : CVal → AVal → CPred}
    (h : ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄) (hQ : ∀ cv av, Q cv av ⊑ Q' cv av) : ⦃P⦄ c ⪯[γ] a ⦃Q'; E⦄ :=
  ⟨PartialOrder.rel_trans h.le_wrp (wrp_mono_post hQ)⟩

theorem Refinement.of_prop {p : Prop} (h : p → ⦃(⊤ : CPred)⦄ c ⪯[γ] a ⦃Q; E⦄) :
    ⦃(⌜p⌝ : CPred)⦄ c ⪯[γ] a ⦃Q; E⦄ :=
  ⟨CompleteLattice.ofProp_le _ _ fun hp => (h hp).le_wrp⟩

theorem Refinement.ite {cond : Prop} [Decidable cond] {c₁ c₂ : CProg} {a₁ a₂ : AProg}
    (h₁ : ⦃P⦄ c₁ ⪯[γ] a₁ ⦃Q; E⦄) (h₂ : ⦃P⦄ c₂ ⪯[γ] a₂ ⦃Q; E⦄) :
    ⦃P⦄ (if cond then c₁ else c₂) ⪯[γ] (if cond then a₁ else a₂) ⦃Q; E⦄ := by
  by_cases hc : cond <;> simp only [hc, ite_true, ite_false] <;> assumption

theorem Refinement.transport [Heyting CPred] {Pa : APred} {Qa : AVal → APred} {Ea : AEPosts}
    (h : ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄) (ha : Triple a Pa Qa Ea) :
    Triple c (P ⊓ γ.pred Pa) (γ.post Q Qa) (EPostsConcretization.ePosts γ E Ea) :=
  ⟨PartialOrder.rel_trans (meet_mono_right (γ.pred_mono ha.le_wp)) (wrp_transport h.le_wrp Qa Ea)⟩

theorem Refinement.conj_wp [Heyting CPred] [WPConjunctive c]
    {R : CVal → CPred} (h : ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄) (hw : P ⊑ wp c R ⊥) :
    ⦃P⦄ c ⪯[γ] a ⦃fun cv av => Q cv av ⊓ R cv; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  have h1 : P ⊓ γ.pred (wp a Qa Ea) ⊑
      wp c (γ.post Q Qa) (EPostsConcretization.ePosts γ E Ea) ⊓
        wp c R (EPostsConcretization.ePosts γ E Ea) :=
    le_meet _ _ _ (wrp_transport h.le_wrp Qa Ea)
      (PartialOrder.rel_trans (meet_le_left _ _) (WP.wp_monotone_bot_le c R _ hw))
  refine PartialOrder.rel_trans h1 ?_
  refine PartialOrder.rel_trans
    (WPConjunctive.wp_meet_wp_le (γ.post Q Qa) R (EPostsConcretization.ePosts γ E Ea)
      (EPostsConcretization.ePosts γ E Ea)) ?_
  refine WP.wp_monotone (x := c) ?_ (meet_le_left _ _)
  intro cv
  rw [meet_apply]
  refine PartialOrder.rel_trans meet_le_comm ?_
  refine PartialOrder.rel_trans
    (meet_iSup_le (R cv) fun av => Q cv av ⊓ γ.pred (Qa av)) ?_
  refine iSup_le _ _ fun av => ?_
  refine PartialOrder.rel_trans ?_ (le_iSup (fun av => (Q cv av ⊓ R cv) ⊓ γ.pred (Qa av)) av)
  exact le_meet _ _ _
    (le_meet _ _ _
      (PartialOrder.rel_trans (meet_le_right _ _) (meet_le_left _ _)) (meet_le_left _ _))
    (PartialOrder.rel_trans (meet_le_right _ _) (meet_le_right _ _))

end

section
variable {CProg : Type _} {AProg : Type v} {CVal AVal : Type _}
  {CPred APred : Type w} {CEPosts AEPosts : Type w'} {ERels : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WP CProg CVal CPred CEPosts] [CCPO AProg] [WP AProg AVal APred AEPosts] [WPCont AProg]
  [EPostsConcretization CPred APred CEPosts AEPosts ERels]
  {γ : Concretization CPred APred}

theorem Refinement.admissible [Heyting CPred]
    (hγ : ∀ (ι : Type v) (X : ι → APred), γ.pred (iSup X) ⊑ iSup fun i => γ.pred (X i))
    (P : CPred) (c : CProg) (Q : CVal → AVal → CPred) (E : ERels) :
    admissible fun a : AProg => ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄ := by
  intro ch hch hall
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  refine PartialOrder.rel_trans (meet_mono_right (γ.pred_mono (WPCont.wp_csup hch Qa Ea))) ?_
  refine PartialOrder.rel_trans (meet_mono_right (hγ _ _)) ?_
  refine PartialOrder.rel_trans (meet_iSup_le _ _) ?_
  exact iSup_le _ _ fun a => wrp_transport (hall a.1 a.2).le_wrp Qa Ea

end

section
variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPosts AEPosts : Type w'}
  {ERels : Type u}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WPMonad CM CPred CEPosts] [WPMonad AM APred AEPosts] [WPMonadExact AM APred AEPosts]
  [EPostsConcretization CPred APred CEPosts AEPosts ERels]
  {γ : Concretization CPred APred}

theorem Refinement.pure {CV AV : Type w} {Q : CV → AV → CPred} {E : ERels} (cv : CV) (av : AV) :
    ⦃Q cv av⦄ (pure cv : CM CV) ⪯[γ] (pure av : AM AV) ⦃Q; E⦄ :=
  ⟨wrp_pure cv av⟩

theorem Refinement.bind [Heyting CPred] {CV AV CV₂ AV₂ : Type w}
    {c₁ : CM CV} {a₁ : AM AV} {c₂ : CV → CM CV₂} {a₂ : AV → AM AV₂}
    {Q : CV₂ → AV₂ → CPred} {E : ERels} :
    ⦃wrp γ c₁ a₁ (wrpCont γ c₂ a₂ Q E) E⦄
      (c₁ >>= c₂) ⪯[γ] (a₁ >>= a₂) ⦃Q; E⦄ :=
  ⟨wrp_bind⟩

theorem Refinement.pure_eq {CV AV : Type w} {f : CV → AV} {E : ERels}
    (P : CPred) (cv : CV) {av : AV} (h : f cv = av) :
    ⦃P⦄ (Pure.pure cv : CM CV) ⪯[γ] (Pure.pure av : AM AV) ⦃fun cv av => ⌜f cv = av⌝; E⦄ :=
  (Refinement.pure cv av).weaken (CompleteLattice.le_ofProp _ _ h)

end

/-! ## Composition of refinements -/

section Comp
universe u₁ u₂

variable {CProg BProg AProg : Type _} {CVal BVal AVal : Type _}
  {CPred BPred APred : Type w} {CEPosts BEPosts AEPosts : Type w'}
  {ERels₁ : Type u₁} {ERels₂ : Type u₂} {ERels : Type u}
  [Assertion CPred] [Assertion BPred] [Assertion APred]
  [Assertion CEPosts] [Assertion BEPosts] [Assertion AEPosts]
  [WP CProg CVal CPred CEPosts] [WP BProg BVal BPred BEPosts] [WP AProg AVal APred AEPosts]
  [EPostsConcretization CPred BPred CEPosts BEPosts ERels₁]
  [EPostsConcretization BPred APred BEPosts AEPosts ERels₂]
  [EPostsConcretization CPred APred CEPosts AEPosts ERels]
  [Heyting BPred] [Heyting CPred]

theorem Refinement.comp
    {γ₁ : Concretization CPred BPred} {γ₂ : Concretization BPred APred}
    {f₁ : CVal → BVal} {f₂ : BVal → AVal} {E₁ : ERels₁} {E₂ : ERels₂} {E : ERels}
    {P : CPred} {P_B : BPred}
    {c : CProg} {b : BProg} {a : AProg}
    (hE : ∀ Ea : AEPosts, EPostsConcretization.ePosts (CEPosts := CEPosts) γ₁ E₁
        (EPostsConcretization.ePosts (CEPosts := BEPosts) γ₂ E₂ Ea)
      = EPostsConcretization.ePosts (CEPosts := CEPosts) (γ₁.comp γ₂) E Ea)
    (hP : ∀ X, P ⊓ γ₁.pred X ⊑ γ₁.pred (P_B ⊓ X))
    (h₂ : ⦃P_B⦄ b ⪯[γ₂] a ⦃fun bv av => ⌜f₂ bv = av⌝; E₂⦄)
    (h₁ : ⦃P⦄ c ⪯[γ₁] b ⦃fun cv bv => ⌜f₁ cv = bv⌝; E₁⦄) :
    ⦃P⦄ c ⪯[γ₁.comp γ₂] a ⦃fun cv av => ⌜f₂ (f₁ cv) = av⌝; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  have hb := wrp_transport h₂.le_wrp Qa Ea
  have hc := wrp_transport h₁.le_wrp (γ₂.post (fun bv av => ⌜f₂ bv = av⌝) Qa)
    (EPostsConcretization.ePosts (CEPosts := BEPosts) γ₂ E₂ Ea)
  rw [hE Ea] at hc
  refine PartialOrder.rel_trans
    (le_meet _ _ _ (meet_le_left _ _)
      (PartialOrder.rel_trans (hP (γ₂.pred (wp a Qa Ea))) (γ₁.pred_mono hb))) ?_
  refine PartialOrder.rel_trans hc ?_
  refine WP.wp_monotone_post (x := c) fun cv => ?_
  simp only [Concretization.post_eq, Concretization.comp, Function.comp]
  exact PartialOrder.rel_refl

theorem Refinement.comp_le
    {γ₁ : Concretization CPred BPred} {γ₂ : Concretization BPred APred}
    {Q₁ : CVal → BVal → CPred} {Q₂ : BVal → AVal → BPred} {Q : CVal → AVal → CPred}
    {E₁ : ERels₁} {E₂ : ERels₂} {E : ERels} {P : CPred} {P_B : BPred}
    {c : CProg} {b : BProg} {a : AProg}
    (hQ : ∀ Qa : AVal → APred, γ₁.post Q₁ (γ₂.post Q₂ Qa) ⊑ (γ₁.comp γ₂).post Q Qa)
    (hE : ∀ Ea : AEPosts, EPostsConcretization.ePosts (CEPosts := CEPosts) γ₁ E₁
        (EPostsConcretization.ePosts (CEPosts := BEPosts) γ₂ E₂ Ea)
      ⊑ EPostsConcretization.ePosts (CEPosts := CEPosts) (γ₁.comp γ₂) E Ea)
    (hP : ∀ X, P ⊓ γ₁.pred X ⊑ γ₁.pred (P_B ⊓ X))
    (h₂ : ⦃P_B⦄ b ⪯[γ₂] a ⦃Q₂; E₂⦄) (h₁ : ⦃P⦄ c ⪯[γ₁] b ⦃Q₁; E₁⦄) :
    ⦃P⦄ c ⪯[γ₁.comp γ₂] a ⦃Q; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  have hb := wrp_transport h₂.le_wrp Qa Ea
  have hc := wrp_transport h₁.le_wrp (γ₂.post Q₂ Qa)
    (EPostsConcretization.ePosts (CEPosts := BEPosts) γ₂ E₂ Ea)
  refine PartialOrder.rel_trans
    (le_meet _ _ _ (meet_le_left _ _)
      (PartialOrder.rel_trans (hP (γ₂.pred (wp a Qa Ea))) (γ₁.pred_mono hb))) ?_
  exact PartialOrder.rel_trans hc (WP.wp_monotone (hQ Qa) (hE Ea))

theorem Concretization.meet_pred_le_pred_top_meet {CPred BPred : Type w}
    [Assertion CPred] [Assertion BPred] (γ : Concretization CPred BPred) (P : CPred) (X : BPred) :
    P ⊓ γ.pred X ⊑ γ.pred (⊤ ⊓ X) :=
  PartialOrder.rel_trans (meet_le_right _ _)
    (γ.pred_mono (le_meet _ _ _ (le_top _) PartialOrder.rel_refl))

end Comp

/-! ## Purification -/

theorem Refinement.purify {CProg σ α : Type} [WP CProg α (σ → Prop) EStack⟨⟩]
    (c : CProg) (v : α) (w : σ)
    (hc : ∀ (Q : α → σ → Prop) (E : EStack⟨⟩), (fun _ => Q v w) ⊑ wp c Q E) :
    ⦃(⊤ : σ → Prop)⦄ c ⪯[Ascent.purify σ] (Pure.pure (v, w) : Id (α × σ)) ⦃purifyRel⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  rw [purify_post]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  refine PartialOrder.rel_trans ?_ (hc (fun cv s => Qa (cv, s)) _)
  exact le_of_forall_le fun s => PartialOrder.rel_refl

/-! ## Exceptions, for `Except` -/

section
variable {εc εa CV AV : Type}
  {γ : Concretization Prop Prop}

theorem Refinement.throw {Q : CV → AV → Prop} {E : εc → εa → Prop} (ec : εc) (ea : εa) :
    ⦃E ec ea⦄ (MonadExceptOf.throw ec : Except εc CV)
      ⪯[γ] (MonadExceptOf.throw ea : Except εa AV) ⦃Q; E⦄ :=
  ⟨wrp_throw ec ea⟩

theorem Refinement.tryCatch {Q : CV → AV → Prop} {E : εc → εa → Prop}
    {cx : Except εc CV} {ax : Except εa AV}
    {ch : εc → Except εc CV} {ah : εa → Except εa AV} :
    ⦃wrp γ cx ax Q (wrpECont γ ch ah Q E)⦄
      (MonadExceptOf.tryCatch cx ch) ⪯[γ] (MonadExceptOf.tryCatch ax ah) ⦃Q; E⦄ :=
  ⟨wrp_tryCatch⟩

end

end Ascent
