import Ascent.Corres.Basic

/-!
# `wrp`: the weakest refinement precondition

`wrp γ c a Q E` is the weakest assertion on the concrete initial state under which the concrete
program `c` refines the abstract program `a` through `γ`: every `wp` fact of `a` transports to
`c`. Each concrete outcome is coupled by `Q : CVal → AVal → CPred` to some abstract outcome
(`∀∃`), and each thrown value by `E`, mirroring `wp x Q E`. `E`'s type `Ξ` is read off the
barrel shapes by `HasEPost`, in two cases: an empty abstract barrel throws nothing, so there is
nothing to couple (`Ξ := EStack⟨⟩`, barrels transported by `γ.ePred`); an aligned exception
layer couples the thrown values (`Ξ := εc → εa → CPred`, the coupling reified through `pred`,
the exceptional mirror of `Concretization.post`).

The four laws are symmetric: `wrp_pure` consumes `Q` and `wrp_throw` consumes `E`; `wrp_bind`
rebinds `Q` with the continuations' `wrp` and `wrp_tryCatch` rebinds `E` with the handlers'
(`throw`/`tryCatch` per effect, here for `Except`). `Refinement c a γ P Q E` is the triple, a
structure with the single field `le_wrp : P ⊑ wrp γ c a Q E` and notation
`⦃P⦄ c ⪯[γ] a ⦃Q; E⦄`. `wrp` is what a tactic manipulates, `Refinement` the user interface.
The triple forms of the laws (`Refinement.bind`, `Refinement.tryCatch`, …) carry the rebound
`wrp` in their preconditions, so they apply to any coupling by instantiation.

An erased concrete step is a leaf that refines `pure v`: scaffolding the abstract program with
the matching `pure` head restores the shared shape for the bind rule, and the monad laws
collapse the scaffold inside the triple (`simp only [pure_bind]`), the judgment being a
predicate on program terms.
-/

open Std.WP Lean.Order

namespace Ascent

universe u v w w'

/-- The type `Ξ` of the exception coupling, read off the pair of barrel shapes, and its
transport into the concrete barrel. Two cases: an empty abstract barrel throws nothing, so
there is nothing to couple; an aligned exception layer couples the thrown values. -/
class HasEPost (CPred : Type w) (APred : Type w) (CEPred : Type w') (AEPred : Type w')
    (Ξ : outParam (Type u))
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred] where
  /-- The exceptional mirror of `post`. -/
  ePost : Concretization CPred APred CEPred AEPred → Ξ → AEPred → CEPred

/-- An empty abstract barrel throws nothing, so there is nothing to couple: the barrel
transport is `ePred` (concrete-only layers are phase data, filled by `ePred`). -/
instance {CPred APred : Type w} {CEPred : Type} [Assertion CPred] [Assertion APred]
    [Assertion CEPred] :
    HasEPost CPred APred CEPred EStack⟨⟩ EStack⟨⟩ where
  ePost γ _ := γ.ePred

/-- Aligned bare exception postconditions, as `Except ε` carries them: the relational
postcondition is `post` at the exception values. -/
noncomputable instance {CPred APred : Type w} {εc εa : Type u}
    [Assertion CPred] [Assertion APred] :
    HasEPost CPred APred (εc → CPred) (εa → APred) (εc → εa → CPred) where
  ePost γ E Ea := γ.post E Ea

/-- Aligned exception layers of a transformer stack: the relational head is `post` at the
exception values; deeper layers are concretized by `ePred`. -/
noncomputable instance {CPred APred : Type w} {εc εa : Type u} {CRest ARest : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion CRest] [Assertion ARest] :
    HasEPost CPred APred ((εc → CPred) × CRest) ((εa → APred) × ARest) (εc → εa → CPred) where
  ePost γ E Ea := (γ.post E Ea.1, (γ.ePred Ea).2)

/-- The exceptional postcondition concretization: reify the relational exceptional
postcondition against the abstract barrel. The exceptional mirror of `post`. -/
noncomputable def Concretization.ePost {CPred APred : Type w} {CEPred AEPred : Type w'}
    {Ξ : Type u}
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
    [HasEPost CPred APred CEPred AEPred Ξ]
    (γ : Concretization CPred APred CEPred AEPred) (E : Ξ) (Ea : AEPred) : CEPred :=
  HasEPost.ePost γ E Ea

@[simp] theorem Concretization.ePost_nil {CPred APred : Type w} {CEPred : Type}
    [Assertion CPred] [Assertion APred] [Assertion CEPred]
    (γ : Concretization CPred APred CEPred EStack⟨⟩) (E Ea : EStack⟨⟩) :
    γ.ePost E Ea = γ.ePred Ea := rfl

@[simp] theorem Concretization.ePost_fun {CPred APred : Type w} {εc εa : Type u}
    [Assertion CPred] [Assertion APred]
    (γ : Concretization CPred APred (εc → CPred) (εa → APred))
    (E : εc → εa → CPred) (Ea : εa → APred) :
    γ.ePost E Ea = γ.post E Ea := rfl

@[simp] theorem Concretization.ePost_cons_head {CPred APred : Type w} {εc εa : Type u}
    {CRest ARest : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion CRest] [Assertion ARest]
    (γ : Concretization CPred APred ((εc → CPred) × CRest) ((εa → APred) × ARest))
    (E : εc → εa → CPred) (Ea : (εa → APred) × ARest) :
    (γ.ePost E Ea).1 = γ.post E Ea.1 := rfl

@[simp] theorem Concretization.ePost_cons_tail {CPred APred : Type w} {εc εa : Type u}
    {CRest ARest : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion CRest] [Assertion ARest]
    (γ : Concretization CPred APred ((εc → CPred) × CRest) ((εa → APred) × ARest))
    (E : εc → εa → CPred) (Ea : (εa → APred) × ARest) :
    (γ.ePost E Ea).2 = (γ.ePred Ea).2 := rfl

/-- Meet distributes over indexed joins in a Heyting lattice. -/
theorem meet_iSup_le {l : Type w} [Assertion l] [Heyting l] {ι : Sort _} (x : l) (f : ι → l) :
    x ⊓ iSup f ⊑ iSup fun i => x ⊓ f i :=
  PartialOrder.rel_trans
    (meet_mono_right (iSup_le _ _ fun i =>
      le_himp_of_meet_le_left (le_iSup (fun i => x ⊓ f i) i)))
    meet_himp_le

section
variable {CProg AProg : Type _} {CVal AVal : Type _}
  {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WP CProg CVal CPred CEPred] [WP AProg AVal APred AEPred]
  [HasEPost CPred APred CEPred AEPred Ξ]

/-- The weakest refinement precondition: the weakest assertion on the concrete initial state
under which `c` refines `a` through `γ`. Every `wp` fact of `a` transports to `c`, coupling each
concrete outcome to some abstract outcome (`∀∃`).
The constant-through-a-proof data (instances, `γ`) comes first, so occurrences share a common
prefix under manipulation by a tactic. -/
noncomputable def wrp (γ : Concretization CPred APred CEPred AEPred)
    (c : CProg) (a : AProg) (Q : CVal → AVal → CPred) (E : Ξ) : CPred :=
  iInf fun Qa : AVal → APred => iInf fun Ea : AEPred =>
    γ.pred (wp a Qa Ea) ⇨ wp c (γ.post Q Qa) (γ.ePost E Ea)

end

/-- The refinement triple: under precondition `P`, the concrete program `c` refines the abstract
program `a` through `γ`, with value coupling `Q` and exception coupling `E`. The binder order
mirrors `Triple`: the programs come first and the instances as late as possible, so that
elaborating an application pins the assertion lattices before `γ` and `Ξ` before `E`. -/
structure Refinement {CProg AProg : Type _} {CVal AVal : Type _}
    {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
    (c : CProg) (a : AProg)
    [WP CProg CVal CPred CEPred] [WP AProg AVal APred AEPred]
    (γ : Concretization CPred APred CEPred AEPred)
    [HasEPost CPred APred CEPred AEPred Ξ]
    (P : CPred) (Q : CVal → AVal → CPred) (E : Ξ) : Prop where
  intro ::
  /-- The precondition entails the weakest refinement precondition. -/
  le_wrp : P ⊑ wrp γ c a Q E

/-- Refinement triple notation without exception coupling (defaults to `⊥`: on coupled barrel
shapes no concrete throw is matched, and an empty coupling telescope `EStack⟨⟩` has `⊥` as its
sole element). -/
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
  {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WP CProg CVal CPred CEPred] [WP AProg AVal APred AEPred]
  [HasEPost CPred APred CEPred AEPred Ξ]

variable {γ : Concretization CPred APred CEPred AEPred} {P : CPred}
  {c : CProg} {a : AProg} {Q : CVal → AVal → CPred} {E : Ξ}

/-- Weaken the precondition. -/
theorem Refinement.weaken {P' : CPred}
    (h : ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄) (hP : P' ⊑ P) : ⦃P'⦄ c ⪯[γ] a ⦃Q; E⦄ :=
  ⟨PartialOrder.rel_trans hP h.le_wrp⟩

/-- Introduction for `wrp`: a precondition that transports each abstract `wp` fact entails the
weakest refinement precondition. This is the forward simulation condition: from a concrete
state satisfying `P` and an abstract postcondition `Qa` that `a` establishes, `c` establishes the
reification of `Qa` through `Q` and `γ`. -/
theorem wrp_intro
    (h : ∀ (Qa : AVal → APred) (Ea : AEPred),
      P ⊓ γ.pred (wp a Qa Ea) ⊑ wp c (γ.post Q Qa) (γ.ePost E Ea)) :
    P ⊑ wrp γ c a Q E :=
  le_iInf _ _ fun Qa => le_iInf _ _ fun Ea =>
    le_himp_of_meet_le_left (PartialOrder.rel_trans meet_le_comm (h Qa Ea))

/-- Elimination for `wrp`: instantiate the weakest refinement precondition at an abstract
postcondition pair, transporting the `wp` fact of `a` to `c`. -/
theorem wrp_transport [Heyting CPred] (h : P ⊑ wrp γ c a Q E)
    (Qa : AVal → APred) (Ea : AEPred) :
    P ⊓ γ.pred (wp a Qa Ea) ⊑ wp c (γ.post Q Qa) (γ.ePost E Ea) :=
  meet_le_of_le_himp
    (PartialOrder.rel_trans h (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea)))

/-- `wrp` is monotone in the value coupling. -/
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

/-- Weaken the value coupling. -/
theorem Refinement.mono_post [Heyting CPred] {Q' : CVal → AVal → CPred}
    (h : ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄) (hQ : ∀ cv av, Q cv av ⊑ Q' cv av) : ⦃P⦄ c ⪯[γ] a ⦃Q'; E⦄ :=
  ⟨PartialOrder.rel_trans h.le_wrp (wrp_mono_post hQ)⟩

/-- Consume a propositional precondition. -/
theorem Refinement.of_prop {p : Prop} (h : p → ⦃(⊤ : CPred)⦄ c ⪯[γ] a ⦃Q; E⦄) :
    ⦃(⌜p⌝ : CPred)⦄ c ⪯[γ] a ⦃Q; E⦄ :=
  ⟨CompleteLattice.ofProp_le _ _ fun hp => (h hp).le_wrp⟩

/-- Branch congruence on a shared condition. -/
theorem Refinement.ite {cond : Prop} [Decidable cond] {c₁ c₂ : CProg} {a₁ a₂ : AProg}
    (h₁ : ⦃P⦄ c₁ ⪯[γ] a₁ ⦃Q; E⦄) (h₂ : ⦃P⦄ c₂ ⪯[γ] a₂ ⦃Q; E⦄) :
    ⦃P⦄ (if cond then c₁ else c₂) ⪯[γ] (if cond then a₁ else a₂) ⦃Q; E⦄ := by
  by_cases hc : cond <;> simp only [hc, ite_true, ite_false] <;> assumption

/-- A concrete `wp` fact rides along in the value coupling: what the concrete program
establishes on normal return strengthens the relational postcondition. -/
theorem Refinement.conj_wp [Heyting CPred] [WPConjunctive c]
    {R : CVal → CPred} (h : ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄) (hw : P ⊑ wp c R ⊥) :
    ⦃P⦄ c ⪯[γ] a ⦃fun cv av => Q cv av ⊓ R cv; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  have h1 : P ⊓ γ.pred (wp a Qa Ea) ⊑
      wp c (γ.post Q Qa) (γ.ePost E Ea) ⊓ wp c R (γ.ePost E Ea) :=
    le_meet _ _ _ (wrp_transport h.le_wrp Qa Ea)
      (PartialOrder.rel_trans (meet_le_left _ _) (WP.wp_monotone_bot_le c R _ hw))
  refine PartialOrder.rel_trans h1 ?_
  refine PartialOrder.rel_trans
    (WPConjunctive.wp_meet_wp_le (γ.post Q Qa) R (γ.ePost E Ea) (γ.ePost E Ea)) ?_
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
variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WPMonad CM CPred CEPred] [WPMonad AM APred AEPred] [WPMonadExact AM APred AEPred]
  [HasEPost CPred APred CEPred AEPred Ξ]
  {γ : Concretization CPred APred CEPred AEPred}

/-- The relational unit law: `pure` consumes the relational postcondition. -/
theorem wrp_pure {CV AV : Type w} {Q : CV → AV → CPred} {E : Ξ} (cv : CV) (av : AV) :
    Q cv av ⊑ wrp γ (pure cv : CM CV) (pure av : AM AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (γ.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_pure_le av Qa Ea)))) ?_
  exact PartialOrder.rel_trans (le_iSup (fun av' => Q cv av' ⊓ γ.pred (Qa av')) av)
    (WPMonad.pure_le_wp_pure cv (γ.post Q Qa) (γ.ePost E Ea))

/-- The relational bind law: `bind` rebinds the relational postcondition with the
continuations' `wrp`; the relational exceptional postcondition threads. -/
theorem wrp_bind [Heyting CPred] {CV AV CV₂ AV₂ : Type w}
    {c₁ : CM CV} {a₁ : AM AV} {c₂ : CV → CM CV₂} {a₂ : AV → AM AV₂}
    {Q : CV₂ → AV₂ → CPred} {E : Ξ} :
    wrp γ c₁ a₁ (fun cv av => wrp γ (c₂ cv) (a₂ av) Q E) E ⊑
      wrp γ (c₁ >>= c₂) (a₁ >>= a₂) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (γ.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_bind_le a₁ a₂ Qa Ea)))) ?_
  refine PartialOrder.rel_trans
    (meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ (fun av => wp (a₂ av) Qa Ea)) (iInf_le _ Ea))) ?_
  refine PartialOrder.rel_trans
    (WP.wp_monotone_post (x := c₁)
      (post' := fun cv => wp (c₂ cv) (γ.post Q Qa) (γ.ePost E Ea)) ?_)
    (WPMonad.bind_le_wp_bind c₁ c₂ (γ.post Q Qa) (γ.ePost E Ea))
  intro cv
  show iSup (fun av => wrp γ (c₂ cv) (a₂ av) Q E ⊓ γ.pred (wp (a₂ av) Qa Ea)) ⊑ _
  refine iSup_le _ _ fun av => ?_
  exact meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))

/-- The triple unit rule: `pure` consumes the value coupling. -/
theorem Refinement.pure {CV AV : Type w} {Q : CV → AV → CPred} {E : Ξ} (cv : CV) (av : AV) :
    ⦃Q cv av⦄ (pure cv : CM CV) ⪯[γ] (pure av : AM AV) ⦃Q; E⦄ :=
  ⟨wrp_pure cv av⟩

/-- The continuations' `wrp`, rebound as a coupling. `wrp_bind`'s rebinding as a combinator:
a tactic that decomposes binds instantiates one short application per step instead of a fresh
lambda. -/
noncomputable def wrpCont {CV AV CV₂ AV₂ : Type w}
    (γ : Concretization CPred APred CEPred AEPred)
    (c₂ : CV → CM CV₂) (a₂ : AV → AM AV₂) (Q : CV₂ → AV₂ → CPred) (E : Ξ) :
    CV → AV → CPred :=
  fun cv av => wrp γ (c₂ cv) (a₂ av) Q E

/-- The triple bind rule: the head's `wrp`, with the continuations' `wrp` rebound as its
coupling, is the precondition. -/
theorem Refinement.bind [Heyting CPred] {CV AV CV₂ AV₂ : Type w}
    {c₁ : CM CV} {a₁ : AM AV} {c₂ : CV → CM CV₂} {a₂ : AV → AM AV₂}
    {Q : CV₂ → AV₂ → CPred} {E : Ξ} :
    ⦃wrp γ c₁ a₁ (wrpCont γ c₂ a₂ Q E) E⦄
      (c₁ >>= c₂) ⪯[γ] (a₁ >>= a₂) ⦃Q; E⦄ :=
  ⟨wrp_bind⟩

/-- The triple unit rule at a functional coupling. -/
theorem Refinement.pure_eq {CV AV : Type w} {f : CV → AV} {E : Ξ}
    (P : CPred) (cv : CV) {av : AV} (h : f cv = av) :
    ⦃P⦄ (Pure.pure cv : CM CV) ⪯[γ] (Pure.pure av : AM AV) ⦃fun cv av => ⌜f cv = av⌝; E⦄ :=
  (Refinement.pure cv av).weaken (CompleteLattice.le_ofProp _ _ h)

end

/-! ## Composition of refinements -/

section Comp
universe u₁ u₂

variable {CProg BProg AProg : Type _} {CVal BVal AVal : Type _}
  {CPred BPred APred : Type w} {CEPred BEPred AEPred : Type w'}
  {Ξ₁ : Type u₁} {Ξ₂ : Type u₂} {Ξ : Type u}
  [Assertion CPred] [Assertion BPred] [Assertion APred]
  [Assertion CEPred] [Assertion BEPred] [Assertion AEPred]
  [WP CProg CVal CPred CEPred] [WP BProg BVal BPred BEPred] [WP AProg AVal APred AEPred]
  [HasEPost CPred BPred CEPred BEPred Ξ₁] [HasEPost BPred APred BEPred AEPred Ξ₂]
  [HasEPost CPred APred CEPred AEPred Ξ]
  [Heyting BPred] [Heyting CPred]

/-- Refinements at functional couplings compose through the composed concretization: the outer
`pred` transports the middle refinement, `hE` aligns the barrel transports (definitional on
delegating shapes). The middle refinement holds unconditionally; a middle-lattice precondition
has no transport into the concrete lattice. -/
theorem Refinement.comp
    {γ₁ : Concretization CPred BPred CEPred BEPred}
    {γ₂ : Concretization BPred APred BEPred AEPred}
    {f₁ : CVal → BVal} {f₂ : BVal → AVal} {E₁ : Ξ₁} {E₂ : Ξ₂} {E : Ξ} {P : CPred}
    {c : CProg} {b : BProg} {a : AProg}
    (hE : ∀ Ea, γ₁.ePost E₁ (γ₂.ePost E₂ Ea) = (γ₁.comp γ₂).ePost E Ea)
    (h₂ : ⦃(⊤ : BPred)⦄ b ⪯[γ₂] a ⦃fun bv av => ⌜f₂ bv = av⌝; E₂⦄)
    (h₁ : ⦃P⦄ c ⪯[γ₁] b ⦃fun cv bv => ⌜f₁ cv = bv⌝; E₁⦄) :
    ⦃P⦄ c ⪯[γ₁.comp γ₂] a ⦃fun cv av => ⌜f₂ (f₁ cv) = av⌝; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  have hb : γ₂.pred (wp a Qa Ea) ⊑
      wp b (γ₂.post (fun bv av => ⌜f₂ bv = av⌝) Qa) (γ₂.ePost E₂ Ea) := by
    have h := wrp_transport h₂.le_wrp Qa Ea
    rwa [Lean.Order.top_meet] at h
  have hc := wrp_transport h₁.le_wrp (γ₂.post (fun bv av => ⌜f₂ bv = av⌝) Qa) (γ₂.ePost E₂ Ea)
  rw [hE Ea] at hc
  refine PartialOrder.rel_trans
    (le_meet _ _ _ (meet_le_left _ _)
      (PartialOrder.rel_trans (meet_le_right _ _) (γ₁.pred_mono hb))) ?_
  refine PartialOrder.rel_trans hc ?_
  refine WP.wp_monotone_post (x := c) fun cv => ?_
  simp only [Concretization.post_eq, Concretization.comp, Function.comp]
  exact PartialOrder.rel_refl

end Comp

/-! ## Purification: dropping the state monad -/

/-- A write-once concrete program (its result `v` and final state `w` are independent of the
initial state) refines the pure return of its result and final state; the terminal coupling
`purifyCouple` reads the exit state into the value. -/
theorem Refinement.purify {CProg σ α : Type} [WP CProg α (σ → Prop) EStack⟨⟩]
    (c : CProg) (v : α) (w : σ)
    (hc : ∀ (Q : α → σ → Prop) (E : EStack⟨⟩), (fun _ => Q v w) ⊑ wp c Q E) :
    ⦃(⊤ : σ → Prop)⦄ c ⪯[Ascent.purify σ] (Pure.pure (v, w) : Id (α × σ)) ⦃purifyCouple⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  rw [purify_post]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  refine PartialOrder.rel_trans ?_ (hc (fun cv s => Qa (cv, s)) _)
  exact le_of_forall_le fun s => PartialOrder.rel_refl


section
variable {εc εa CV AV : Type}
  {γ : Concretization Prop Prop (εc → Prop) (εa → Prop)}

/-- The relational throw law: `throw` consumes the relational exceptional postcondition,
exactly as `pure` consumes the relational postcondition. -/
theorem wrp_throw {Q : CV → AV → Prop} {E : εc → εa → Prop} (ec : εc) (ea : εa) :
    E ec ea ⊑
      wrp γ (MonadExceptOf.throw ec : Except εc CV)
        (MonadExceptOf.throw ea : Except εa AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  simp only [WPMonad.wp_throw_Except_apply_eq, Concretization.ePost_fun]
  exact le_iSup_of_le ea PartialOrder.rel_refl

/-- The relational tryCatch law: `tryCatch` rebinds the relational exceptional postcondition
with the handlers' `wrp`, exactly as `bind` rebinds the relational postcondition; the
relational postcondition threads. -/
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

/-- The handlers' `wrp`, rebound as an exception coupling. The exceptional mirror of `wrpCont`:
a tactic that decomposes `tryCatch` instantiates one short application per step instead of a
fresh lambda. -/
noncomputable def wrpECont
    (γ : Concretization Prop Prop (εc → Prop) (εa → Prop))
    (ch : εc → Except εc CV) (ah : εa → Except εa AV) (Q : CV → AV → Prop)
    (E : εc → εa → Prop) : εc → εa → Prop :=
  fun ec ea => wrp γ (ch ec) (ah ea) Q E

/-- The triple throw rule: `throw` consumes the exception coupling. -/
theorem Refinement.throw {Q : CV → AV → Prop} {E : εc → εa → Prop} (ec : εc) (ea : εa) :
    ⦃E ec ea⦄ (MonadExceptOf.throw ec : Except εc CV)
      ⪯[γ] (MonadExceptOf.throw ea : Except εa AV) ⦃Q; E⦄ :=
  ⟨wrp_throw ec ea⟩

/-- The triple tryCatch rule: the body's `wrp`, with the handlers' `wrp` rebound as its
exception coupling, is the precondition. -/
theorem Refinement.tryCatch {Q : CV → AV → Prop} {E : εc → εa → Prop}
    {cx : Except εc CV} {ax : Except εa AV}
    {ch : εc → Except εc CV} {ah : εa → Except εa AV} :
    ⦃wrp γ cx ax Q (wrpECont γ ch ah Q E)⦄
      (MonadExceptOf.tryCatch cx ch) ⪯[γ] (MonadExceptOf.tryCatch ax ah) ⦃Q; E⦄ :=
  ⟨wrp_tryCatch⟩

end

end Ascent
