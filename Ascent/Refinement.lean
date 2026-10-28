import Ascent.EPosts

/-!
# The refinement judgment

`wrp γ c a Q E` is the weakest refinement precondition: the weakest concrete assertion under
which the concrete program `c` refines the abstract program `a`.

```
wrp γ c a Q E = ⨅ Qa Ea, γ.pred (wp a Qa Ea) ⇨ wp c (γ.post Q Qa) (HasEPost.ePosts γ E Ea)
```

Read it as transport. For every abstract postcondition pair `(Qa, Ea)`, if `a` establishes it,
then `c` establishes its concretization. `Q : CVal → AVal → CPred` couples returned values, and
`E` couples thrown values. `HasEPost` reads the type `Ξ` of `E` off the exception stacks.

`Refinement c a γ P Q E` is the triple `P ⊑ wrp γ c a Q E`, written `⦃P⦄ c ⪯[γ] a ⦃Q; E⦄`.
`wrp_intro` and `wrp_transport` convert between the triple and the transport statement.

The laws of `wrp` follow the laws of `wp`. `wrp_pure` consumes `Q`, and `wrp_bind` rebinds `Q`
with the `wrp` of the continuations. `wrp_throw` consumes `E`, and `wrp_tryCatch` rebinds `E`
with the `wrp` of the handlers. The `Refinement` forms of the laws carry the rebound `wrp` in
the precondition, so they apply to every coupling by instantiation.
-/

open Std.WP Lean.Order

namespace Ascent

universe u v w w'

theorem meet_iSup_le {l : Type w} [Assertion l] [Heyting l] {ι : Sort _} (x : l) (f : ι → l) :
    x ⊓ iSup f ⊑ iSup fun i => x ⊓ f i :=
  PartialOrder.rel_trans
    (meet_mono_right (iSup_le _ _ fun i =>
      le_himp_of_meet_le_left (le_iSup (fun i => x ⊓ f i) i)))
    meet_himp_le

section
variable {CProg AProg : Type _} {CVal AVal : Type _}
  {CPred APred : Type w} {CEPosts AEPosts : Type w'} {Ξ : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WP CProg CVal CPred CEPosts] [WP AProg AVal APred AEPosts]
  [HasEPost CPred APred CEPosts AEPosts Ξ]

/-- The weakest concrete assertion under which `c` refines `a`: every `wp` fact of `a`
transports to `c` through `γ`, `Q` and `E`. -/
noncomputable def wrp (γ : Concretization CPred APred CEPosts AEPosts)
    (c : CProg) (a : AProg) (Q : CVal → AVal → CPred) (E : Ξ) : CPred :=
  iInf fun Qa : AVal → APred => iInf fun Ea : AEPosts =>
    γ.pred (wp a Qa Ea) ⇨ wp c (γ.post Q Qa) (HasEPost.ePosts γ E Ea)

end

/-- The refinement triple `P ⊑ wrp γ c a Q E`, written `⦃P⦄ c ⪯[γ] a ⦃Q; E⦄`. -/
structure Refinement {CProg AProg : Type _} {CVal AVal : Type _}
    {CPred APred : Type w} {CEPosts AEPosts : Type w'} {Ξ : Type u}
    [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
    (c : CProg) (a : AProg)
    [WP CProg CVal CPred CEPosts] [WP AProg AVal APred AEPosts]
    (γ : Concretization CPred APred CEPosts AEPosts)
    [HasEPost CPred APred CEPosts AEPosts Ξ]
    (P : CPred) (Q : CVal → AVal → CPred) (E : Ξ) : Prop where
  intro ::
  /-- The precondition entails the weakest refinement precondition. -/
  le_wrp : P ⊑ wrp γ c a Q E

/-- The triple without an exception coupling. `E` is `⊥`. -/
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
  {CPred APred : Type w} {CEPosts AEPosts : Type w'} {Ξ : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WP CProg CVal CPred CEPosts] [WP AProg AVal APred AEPosts]
  [HasEPost CPred APred CEPosts AEPosts Ξ]

variable {γ : Concretization CPred APred CEPosts AEPosts} {P : CPred}
  {c : CProg} {a : AProg} {Q : CVal → AVal → CPred} {E : Ξ}

theorem Refinement.weaken {P' : CPred}
    (h : ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄) (hP : P' ⊑ P) : ⦃P'⦄ c ⪯[γ] a ⦃Q; E⦄ :=
  ⟨PartialOrder.rel_trans hP h.le_wrp⟩

theorem wrp_intro
    (h : ∀ (Qa : AVal → APred) (Ea : AEPosts),
      P ⊓ γ.pred (wp a Qa Ea) ⊑ wp c (γ.post Q Qa) (HasEPost.ePosts γ E Ea)) :
    P ⊑ wrp γ c a Q E :=
  le_iInf _ _ fun Qa => le_iInf _ _ fun Ea =>
    le_himp_of_meet_le_left (PartialOrder.rel_trans meet_le_comm (h Qa Ea))

theorem wrp_transport [Heyting CPred] (h : P ⊑ wrp γ c a Q E)
    (Qa : AVal → APred) (Ea : AEPosts) :
    P ⊓ γ.pred (wp a Qa Ea) ⊑ wp c (γ.post Q Qa) (HasEPost.ePosts γ E Ea) :=
  meet_le_of_le_himp
    (PartialOrder.rel_trans h (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea)))

theorem wrp_mono_post [Heyting CPred] {Q' : CVal → AVal → CPred}
    (hQ : ∀ cv av, Q cv av ⊑ Q' cv av) : wrp γ c a Q E ⊑ wrp γ c a Q' E := by
  refine iInf_mono fun Qa => iInf_mono fun Ea => ?_
  refine himp_mono PartialOrder.rel_refl ?_
  refine WP.wp_monotone_post (x := c) ?_
  intro cv
  refine iSup_le _ _ fun av => ?_
  exact PartialOrder.rel_trans
    (le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) (hQ cv av)) (meet_le_right _ _))
    (le_iSup (fun av' => Q' cv av' ⊓ γ.pred (Qa av')) av)

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

theorem Refinement.conj_wp [Heyting CPred] [WPConjunctive c]
    {R : CVal → CPred} (h : ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄) (hw : P ⊑ wp c R ⊥) :
    ⦃P⦄ c ⪯[γ] a ⦃fun cv av => Q cv av ⊓ R cv; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  have h1 : P ⊓ γ.pred (wp a Qa Ea) ⊑
      wp c (γ.post Q Qa) (HasEPost.ePosts γ E Ea) ⊓ wp c R (HasEPost.ePosts γ E Ea) :=
    le_meet _ _ _ (wrp_transport h.le_wrp Qa Ea)
      (PartialOrder.rel_trans (meet_le_left _ _) (WP.wp_monotone_bot_le c R _ hw))
  refine PartialOrder.rel_trans h1 ?_
  refine PartialOrder.rel_trans
    (WPConjunctive.wp_meet_wp_le (γ.post Q Qa) R (HasEPost.ePosts γ E Ea) (HasEPost.ePosts γ E Ea)) ?_
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
variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPosts AEPosts : Type w'} {Ξ : Type u}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WPMonad CM CPred CEPosts] [WPMonad AM APred AEPosts] [WPMonadExact AM APred AEPosts]
  [HasEPost CPred APred CEPosts AEPosts Ξ]
  {γ : Concretization CPred APred CEPosts AEPosts}

theorem wrp_pure {CV AV : Type w} {Q : CV → AV → CPred} {E : Ξ} (cv : CV) (av : AV) :
    Q cv av ⊑ wrp γ (pure cv : CM CV) (pure av : AM AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (γ.pred_mono ((‹WPMonadExact AM APred AEPosts›).wp_pure_le av Qa Ea)))) ?_
  exact PartialOrder.rel_trans (le_iSup (fun av' => Q cv av' ⊓ γ.pred (Qa av')) av)
    (WPMonad.pure_le_wp_pure cv (γ.post Q Qa) (HasEPost.ePosts γ E Ea))

theorem wrp_bind [Heyting CPred] {CV AV CV₂ AV₂ : Type w}
    {c₁ : CM CV} {a₁ : AM AV} {c₂ : CV → CM CV₂} {a₂ : AV → AM AV₂}
    {Q : CV₂ → AV₂ → CPred} {E : Ξ} :
    wrp γ c₁ a₁ (fun cv av => wrp γ (c₂ cv) (a₂ av) Q E) E ⊑
      wrp γ (c₁ >>= c₂) (a₁ >>= a₂) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (γ.pred_mono ((‹WPMonadExact AM APred AEPosts›).wp_bind_le a₁ a₂ Qa Ea)))) ?_
  refine PartialOrder.rel_trans
    (meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ (fun av => wp (a₂ av) Qa Ea)) (iInf_le _ Ea))) ?_
  refine PartialOrder.rel_trans
    (WP.wp_monotone_post (x := c₁)
      (post' := fun cv => wp (c₂ cv) (γ.post Q Qa) (HasEPost.ePosts γ E Ea)) ?_)
    (WPMonad.bind_le_wp_bind c₁ c₂ (γ.post Q Qa) (HasEPost.ePosts γ E Ea))
  intro cv
  show iSup (fun av => wrp γ (c₂ cv) (a₂ av) Q E ⊓ γ.pred (wp (a₂ av) Qa Ea)) ⊑ _
  refine iSup_le _ _ fun av => ?_
  exact meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))

theorem Refinement.pure {CV AV : Type w} {Q : CV → AV → CPred} {E : Ξ} (cv : CV) (av : AV) :
    ⦃Q cv av⦄ (pure cv : CM CV) ⪯[γ] (pure av : AM AV) ⦃Q; E⦄ :=
  ⟨wrp_pure cv av⟩

/-- The `wrp` of the continuations `c₂` and `a₂`, as a coupling on their inputs. -/
noncomputable def wrpCont {CV AV CV₂ AV₂ : Type w}
    (γ : Concretization CPred APred CEPosts AEPosts)
    (c₂ : CV → CM CV₂) (a₂ : AV → AM AV₂) (Q : CV₂ → AV₂ → CPred) (E : Ξ) :
    CV → AV → CPred :=
  fun cv av => wrp γ (c₂ cv) (a₂ av) Q E

theorem Refinement.bind [Heyting CPred] {CV AV CV₂ AV₂ : Type w}
    {c₁ : CM CV} {a₁ : AM AV} {c₂ : CV → CM CV₂} {a₂ : AV → AM AV₂}
    {Q : CV₂ → AV₂ → CPred} {E : Ξ} :
    ⦃wrp γ c₁ a₁ (wrpCont γ c₂ a₂ Q E) E⦄
      (c₁ >>= c₂) ⪯[γ] (a₁ >>= a₂) ⦃Q; E⦄ :=
  ⟨wrp_bind⟩

theorem Refinement.pure_eq {CV AV : Type w} {f : CV → AV} {E : Ξ}
    (P : CPred) (cv : CV) {av : AV} (h : f cv = av) :
    ⦃P⦄ (Pure.pure cv : CM CV) ⪯[γ] (Pure.pure av : AM AV) ⦃fun cv av => ⌜f cv = av⌝; E⦄ :=
  (Refinement.pure cv av).weaken (CompleteLattice.le_ofProp _ _ h)

end

/-! ## Composition of refinements -/

section Comp
universe u₁ u₂

variable {CProg BProg AProg : Type _} {CVal BVal AVal : Type _}
  {CPred BPred APred : Type w} {CEPosts BEPosts AEPosts : Type w'}
  {Ξ₁ : Type u₁} {Ξ₂ : Type u₂} {Ξ : Type u}
  [Assertion CPred] [Assertion BPred] [Assertion APred]
  [Assertion CEPosts] [Assertion BEPosts] [Assertion AEPosts]
  [WP CProg CVal CPred CEPosts] [WP BProg BVal BPred BEPosts] [WP AProg AVal APred AEPosts]
  [HasEPost CPred BPred CEPosts BEPosts Ξ₁] [HasEPost BPred APred BEPosts AEPosts Ξ₂]
  [HasEPost CPred APred CEPosts AEPosts Ξ]
  [Heyting BPred] [Heyting CPred]

theorem Refinement.comp
    {γ₁ : Concretization CPred BPred CEPosts BEPosts}
    {γ₂ : Concretization BPred APred BEPosts AEPosts}
    {f₁ : CVal → BVal} {f₂ : BVal → AVal} {E₁ : Ξ₁} {E₂ : Ξ₂} {E : Ξ} {P : CPred}
    {c : CProg} {b : BProg} {a : AProg}
    (hE : ∀ Ea, HasEPost.ePosts γ₁ E₁ (HasEPost.ePosts γ₂ E₂ Ea) = HasEPost.ePosts (γ₁.comp γ₂) E Ea)
    (h₂ : ⦃(⊤ : BPred)⦄ b ⪯[γ₂] a ⦃fun bv av => ⌜f₂ bv = av⌝; E₂⦄)
    (h₁ : ⦃P⦄ c ⪯[γ₁] b ⦃fun cv bv => ⌜f₁ cv = bv⌝; E₁⦄) :
    ⦃P⦄ c ⪯[γ₁.comp γ₂] a ⦃fun cv av => ⌜f₂ (f₁ cv) = av⌝; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  have hb : γ₂.pred (wp a Qa Ea) ⊑
      wp b (γ₂.post (fun bv av => ⌜f₂ bv = av⌝) Qa) (HasEPost.ePosts γ₂ E₂ Ea) := by
    have h := wrp_transport h₂.le_wrp Qa Ea
    rwa [Lean.Order.top_meet] at h
  have hc := wrp_transport h₁.le_wrp (γ₂.post (fun bv av => ⌜f₂ bv = av⌝) Qa) (HasEPost.ePosts γ₂ E₂ Ea)
  rw [hE Ea] at hc
  refine PartialOrder.rel_trans
    (le_meet _ _ _ (meet_le_left _ _)
      (PartialOrder.rel_trans (meet_le_right _ _) (γ₁.pred_mono hb))) ?_
  refine PartialOrder.rel_trans hc ?_
  refine WP.wp_monotone_post (x := c) fun cv => ?_
  simp only [Concretization.post_eq, Concretization.comp, Function.comp]
  exact PartialOrder.rel_refl

end Comp

/-! ## Purification -/

theorem Refinement.purify {CProg σ α : Type} [WP CProg α (σ → Prop) EStack⟨⟩]
    (c : CProg) (v : α) (w : σ)
    (hc : ∀ (Q : α → σ → Prop) (E : EStack⟨⟩), (fun _ => Q v w) ⊑ wp c Q E) :
    ⦃(⊤ : σ → Prop)⦄ c ⪯[Ascent.purify σ] (Pure.pure (v, w) : Id (α × σ)) ⦃purifyCouple⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  rw [purify_post]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  refine PartialOrder.rel_trans ?_ (hc (fun cv s => Qa (cv, s)) _)
  exact le_of_forall_le fun s => PartialOrder.rel_refl

/-! ## Exceptions, for `Except` -/

section
variable {εc εa CV AV : Type}
  {γ : Concretization Prop Prop (εc → Prop) (εa → Prop)}

theorem wrp_throw {Q : CV → AV → Prop} {E : εc → εa → Prop} (ec : εc) (ea : εa) :
    E ec ea ⊑
      wrp γ (MonadExceptOf.throw ec : Except εc CV)
        (MonadExceptOf.throw ea : Except εa AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  simp only [WPMonad.wp_throw_Except_apply_eq, HasEPost.ePosts_fun]
  exact le_iSup_of_le ea PartialOrder.rel_refl

theorem wrp_tryCatch {Q : CV → AV → Prop} {E : εc → εa → Prop}
    {cx : Except εc CV} {ax : Except εa AV}
    {ch : εc → Except εc CV} {ah : εa → Except εa AV} :
    wrp γ cx ax Q (fun ec ea => wrp γ (ch ec) (ah ea) Q E) ⊑
      wrp γ (MonadExceptOf.tryCatch cx ch) (MonadExceptOf.tryCatch ax ah) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  simp only [WPMonad.wp_tryCatch_Except_apply_eq]
  refine PartialOrder.rel_trans
    (meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ Qa)
        (iInf_le _ (fun ea => wp (ah ea) Qa Ea)))) ?_
  refine WP.wp_monotone (x := cx) PartialOrder.rel_refl ?_
  intro ec
  show iSup (fun ea => wrp γ (ch ec) (ah ea) Q E ⊓ γ.pred (wp (ah ea) Qa Ea)) ⊑ _
  refine iSup_le _ _ fun ea => ?_
  exact meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))

end

section
variable {εc εa CV AV : Type}
  {γ : Concretization Prop Prop (εc → Prop) (εa → Prop)}

/-- The `wrp` of the handlers `ch` and `ah`, as a coupling on thrown values. -/
noncomputable def wrpECont
    (γ : Concretization Prop Prop (εc → Prop) (εa → Prop))
    (ch : εc → Except εc CV) (ah : εa → Except εa AV) (Q : CV → AV → Prop)
    (E : εc → εa → Prop) : εc → εa → Prop :=
  fun ec ea => wrp γ (ch ec) (ah ea) Q E

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
