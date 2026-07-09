import Ascent.Corres.Basic

/-!
# `rwp`: the weakest precondition of refinement

`rwp γ a c Q E` is the weakest concrete-state precondition under which the abstract program
`a` is refined by the concrete program `c` through `γ`: every abstract `wp` fact transports,
so each concrete outcome is coupled by `Q : AVal → CVal → CPred` to some abstract outcome
(`∀∃` refinement) and each thrown value by `E`, mirroring `wp x Q E`. `E`'s type `Ξ` is read
off the barrel shapes by `HasEPost`, in two cases: an empty abstract barrel throws nothing, so
there is nothing to couple (`Ξ := EPost.Nil`, barrels transported by `γ.ePred`); an aligned
exception layer couples the thrown values (`Ξ := εa → εc → CPred`, the coupling reified
through `pred` — the exceptional mirror of `Concretization.post`).

The four laws are exactly symmetric: `rwp_pure` consumes `Q` and `rwp_throw` consumes `E`;
`rwp_bind` rebinds `Q` with the continuations' `rwp` and `rwp_tryCatch` rebinds `E` with the
handlers' (`throw`/`tryCatch` per effect, here for `Except`). `RTriple a c γ P Q E` is the
triple-shaped judgment `P ⊑ rwp γ a c Q E`, with notation `⦃P⦄ a ⊑[γ] c ⦃Q; E⦄`;
`rwp` is what a refinement tactic manipulates, `RTriple` the user interface.
-/

open Std.Internal.Do Lean.Order

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
    HasEPost CPred APred CEPred EPost.Nil EPost.Nil where
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

@[simp] theorem Concretization.ePost_nil {CPred APred : Type w} {CEPred : Type}
    [Assertion CPred] [Assertion APred] [Assertion CEPred]
    (γ : Concretization CPred APred CEPred EPost.Nil) (E Ea : EPost.Nil) :
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

/-- Meet distributes over indexed joins in a frame. -/
theorem meet_iSup_le {l : Type w} [Assertion l] [Frame l] {ι : Sort _} (x : l) (f : ι → l) :
    x ⊓ iSup f ⊑ iSup fun i => x ⊓ f i :=
  PartialOrder.rel_trans
    (CompleteLattice.meet_mono_right (iSup_le _ _ fun i =>
      CompleteLattice.le_himp_of_meet_le_comm (le_iSup (fun i => x ⊓ f i) i)))
    CompleteLattice.meet_himp_le

section
variable {CProg AProg : Type _} {CVal AVal : Type _}
  {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WP CProg CVal CPred CEPred] [WP AProg AVal APred AEPred]
  [HasEPost CPred APred CEPred AEPred Ξ]

/-- The weakest precondition under which `a` is refined by `c` through `γ`: every abstract
`wp` fact transports, coupling each concrete outcome to some abstract outcome (`∀∃`
refinement).
The constant-through-a-proof data (instances, `γ`) comes first, so occurrences share a common
prefix under manipulation by a tactic. -/
noncomputable def rwp (γ : Concretization CPred APred CEPred AEPred)
    (a : AProg) (c : CProg) (Q : AVal → CVal → CPred) (E : Ξ) : CPred :=
  iInf fun Qa : AVal → APred => iInf fun Ea : AEPred =>
    γ.pred (wp a Qa Ea) ⇨ wp c (γ.post Q Qa) (γ.ePost E Ea)

end

/-- The refinement triple: under precondition `P`, the abstract program `a` is refined by the
concrete program `c` through `γ`, with value coupling `Q` and exception coupling `E`. The
binder order mirrors `Triple`: the programs come first and the instances as late as possible,
so that elaborating an application pins the assertion lattices before `γ` and `Ξ` before `E`. -/
def RTriple {CProg AProg : Type _} {CVal AVal : Type _}
    {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
    (a : AProg) (c : CProg)
    [WP AProg AVal APred AEPred] [WP CProg CVal CPred CEPred]
    (γ : Concretization CPred APred CEPred AEPred)
    [HasEPost CPred APred CEPred AEPred Ξ]
    (P : CPred) (Q : AVal → CVal → CPred) (E : Ξ) : Prop :=
  P ⊑ rwp γ a c Q E

/-- Refinement triple notation without exception coupling (defaults to `⊥`: on coupled barrel
shapes no concrete throw is matched, and an empty coupling telescope `EPost.Nil` has `⊥` as its
sole element). -/
scoped syntax:lead atomic("⦃ " term " ⦄ " term:max " ⊑[") term "] " term:max
  " ⦃ " term " ⦄" : term

@[inherit_doc RTriple]
scoped syntax:lead atomic("⦃ " term " ⦄ " term:max " ⊑[") term "] " term:max
  " ⦃ " term "; " term " ⦄" : term

scoped macro_rules
  | `(⦃ $P ⦄ $a ⊑[$γ] $c ⦃ $Q ⦄) => `(RTriple $a $c $γ $P $Q Lean.Order.bot)
  | `(⦃ $P ⦄ $a ⊑[$γ] $c ⦃ $Q; $E ⦄) => `(RTriple $a $c $γ $P $Q $E)

section
variable {CProg AProg : Type _} {CVal AVal : Type _}
  {CPred APred : Type w} {CEPred AEPred : Type w'} {Ξ : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WP CProg CVal CPred CEPred] [WP AProg AVal APred AEPred]
  [HasEPost CPred APred CEPred AEPred Ξ]

variable {γ : Concretization CPred APred CEPred AEPred} {P : CPred}
  {a : AProg} {c : CProg} {Q : AVal → CVal → CPred} {E : Ξ}

/-- Weaken the precondition. -/
theorem RTriple.weaken {P' : CPred}
    (h : ⦃P⦄ a ⊑[γ] c ⦃Q; E⦄) (hP : P' ⊑ P) : ⦃P'⦄ a ⊑[γ] c ⦃Q; E⦄ :=
  PartialOrder.rel_trans hP h

/-- Introduction, unfolded: a refinement triple transports each abstract `wp` fact under the
precondition. -/
theorem RTriple.intro
    (h : ∀ (Qa : AVal → APred) (Ea : AEPred),
      P ⊓ γ.pred (wp a Qa Ea) ⊑ wp c (γ.post Q Qa) (γ.ePost E Ea)) :
    ⦃P⦄ a ⊑[γ] c ⦃Q; E⦄ :=
  le_iInf _ _ fun Qa => le_iInf _ _ fun Ea =>
    himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm (h Qa Ea))

/-- Elimination, unfolded: instantiate a refinement triple at an abstract postcondition pair. -/
theorem RTriple.elim [Frame CPred] (h : ⦃P⦄ a ⊑[γ] c ⦃Q; E⦄)
    (Qa : AVal → APred) (Ea : AEPred) :
    P ⊓ γ.pred (wp a Qa Ea) ⊑ wp c (γ.post Q Qa) (γ.ePost E Ea) :=
  CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans h (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea)))

/-- `rwp` is monotone in the value coupling. -/
theorem rwp_mono_post [Frame CPred] {Q' : AVal → CVal → CPred}
    (hQ : ∀ av cv, Q av cv ⊑ Q' av cv) : rwp γ a c Q E ⊑ rwp γ a c Q' E := by
  refine CompleteLattice.iInf_mono fun Qa => CompleteLattice.iInf_mono fun Ea => ?_
  refine CompleteLattice.himp_mono PartialOrder.rel_refl ?_
  refine WP.wp_consequence c _ _ _ ?_
  intro cv
  refine iSup_le _ _ fun av => ?_
  exact PartialOrder.rel_trans
    (le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) (hQ av cv)) (meet_le_right _ _))
    (le_iSup (fun av' => Q' av' cv ⊓ γ.pred (Qa av')) av)

/-- Weaken the value coupling. -/
theorem RTriple.mono_post [Frame CPred] {Q' : AVal → CVal → CPred}
    (h : ⦃P⦄ a ⊑[γ] c ⦃Q; E⦄) (hQ : ∀ av cv, Q av cv ⊑ Q' av cv) : ⦃P⦄ a ⊑[γ] c ⦃Q'; E⦄ :=
  PartialOrder.rel_trans h (rwp_mono_post hQ)

/-- Consume a propositional precondition. -/
theorem RTriple.of_prop {p : Prop} (h : p → ⦃(⊤ : CPred)⦄ a ⊑[γ] c ⦃Q; E⦄) :
    ⦃(⌜p⌝ : CPred)⦄ a ⊑[γ] c ⦃Q; E⦄ :=
  ofProp_le _ _ h

/-- Branch congruence on a shared condition. -/
theorem RTriple.ite {cond : Prop} [Decidable cond] {a₁ a₂ : AProg} {c₁ c₂ : CProg}
    (h₁ : ⦃P⦄ a₁ ⊑[γ] c₁ ⦃Q; E⦄) (h₂ : ⦃P⦄ a₂ ⊑[γ] c₂ ⦃Q; E⦄) :
    ⦃P⦄ (if cond then a₁ else a₂) ⊑[γ] (if cond then c₁ else c₂) ⦃Q; E⦄ := by
  by_cases hc : cond <;> simp only [hc, if_true, if_false] <;> assumption

/-- A concrete `wp` fact rides along in the value coupling: what the concrete program
establishes on normal return strengthens the relational postcondition. -/
theorem RTriple.conj_wp [Frame CPred] [WPConjunctive CProg CVal CPred CEPred]
    {R : CVal → CPred} (h : ⦃P⦄ a ⊑[γ] c ⦃Q; E⦄) (hw : P ⊑ wp c R ⊥) :
    ⦃P⦄ a ⊑[γ] c ⦃fun av cv => Q av cv ⊓ R cv; E⦄ := by
  refine RTriple.intro fun Qa Ea => ?_
  have h1 : P ⊓ γ.pred (wp a Qa Ea) ⊑
      wp c (γ.post Q Qa) (γ.ePost E Ea) ⊓ wp c R (γ.ePost E Ea) :=
    le_meet _ _ _ (h.elim Qa Ea)
      (PartialOrder.rel_trans (meet_le_left _ _) (WP.wp_econs_bot_le c R _ hw))
  refine PartialOrder.rel_trans h1 ?_
  refine PartialOrder.rel_trans
    (WPConjunctive.wp_meet_wp_le c (γ.post Q Qa) R (γ.ePost E Ea)) ?_
  refine WP.wp_consequence c _ _ _ fun cv => ?_
  rw [meet_apply]
  refine PartialOrder.rel_trans CompleteLattice.meet_le_comm ?_
  refine PartialOrder.rel_trans
    (meet_iSup_le (R cv) fun av => Q av cv ⊓ γ.pred (Qa av)) ?_
  refine iSup_le _ _ fun av => ?_
  refine PartialOrder.rel_trans ?_ (le_iSup (fun av => (Q av cv ⊓ R cv) ⊓ γ.pred (Qa av)) av)
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
theorem rwp_pure {AV CV : Type w} {Q : AV → CV → CPred} {E : Ξ} (av : AV) (cv : CV) :
    Q av cv ⊑ rwp γ (pure av : AM AV) (pure cv : CM CV) Q E := by
  refine RTriple.intro fun Qa Ea => ?_
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (γ.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_pure_le av Qa Ea)))) ?_
  exact PartialOrder.rel_trans (le_iSup (fun av' => Q av' cv ⊓ γ.pred (Qa av')) av)
    (WPMonad.pure_le_wp_pure cv (γ.post Q Qa) (γ.ePost E Ea))

/-- The relational bind law: `bind` rebinds the relational postcondition with the
continuations' `rwp`; the relational exceptional postcondition threads. -/
theorem rwp_bind [Frame CPred] {CV AV CV₂ AV₂ : Type w}
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {Q : AV₂ → CV₂ → CPred} {E : Ξ} :
    rwp γ a₁ c₁ (fun av cv => rwp γ (a₂ av) (c₂ cv) Q E) E ⊑
      rwp γ (a₁ >>= a₂) (c₁ >>= c₂) Q E := by
  refine RTriple.intro fun Qa Ea => ?_
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
  show iSup (fun av => rwp γ (a₂ av) (c₂ cv) Q E ⊓ γ.pred (wp (a₂ av) Qa Ea)) ⊑ _
  refine iSup_le _ _ fun av => ?_
  exact CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))

/-- The triple unit rule: `pure` consumes the value coupling. -/
theorem RTriple.pure {AV CV : Type w} {Q : AV → CV → CPred} {E : Ξ} (av : AV) (cv : CV) :
    ⦃Q av cv⦄ (pure av : AM AV) ⊑[γ] (pure cv : CM CV) ⦃Q; E⦄ :=
  rwp_pure av cv

/-- The triple bind rule, post-parametric form: the head's value coupling is the
continuations' `rwp`. -/
theorem RTriple.bind [Frame CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {Q : AV₂ → CV₂ → CPred} {E : Ξ}
    (h : ⦃P⦄ a₁ ⊑[γ] c₁ ⦃fun av cv => rwp γ (a₂ av) (c₂ cv) Q E; E⦄) :
    ⦃P⦄ (a₁ >>= a₂) ⊑[γ] (c₁ >>= c₂) ⦃Q; E⦄ :=
  PartialOrder.rel_trans h rwp_bind

/-- The triple bind rule, mid-coupling form: the head establishes `R`, the continuations
correspond under it. -/
theorem RTriple.bind' [Frame CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {R : AV → CV → CPred} {Q : AV₂ → CV₂ → CPred} {E : Ξ}
    (h₁ : ⦃P⦄ a₁ ⊑[γ] c₁ ⦃R; E⦄)
    (h₂ : ∀ av cv, ⦃R av cv⦄ (a₂ av) ⊑[γ] (c₂ cv) ⦃Q; E⦄) :
    ⦃P⦄ (a₁ >>= a₂) ⊑[γ] (c₁ >>= c₂) ⦃Q; E⦄ :=
  .bind (PartialOrder.rel_trans h₁ (rwp_mono_post h₂))

/-- The triple unit rule at a functional coupling. -/
theorem RTriple.pure_eq {AV CV : Type w} {f : CV → AV} {E : Ξ}
    (P : CPred) {av : AV} (cv : CV) (h : f cv = av) :
    ⦃P⦄ (Pure.pure av : AM AV) ⊑[γ] (Pure.pure cv : CM CV) ⦃fun av cv => ⌜av = f cv⌝; E⦄ :=
  (RTriple.pure av cv).weaken (le_ofProp _ _ h.symm)

/-- The triple bind rule at a functional head coupling: the continuations correspond at each
concrete value and its coupled abstract value. -/
theorem RTriple.bind_eq [Frame CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
    {f : CV → AV} {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {Q : AV₂ → CV₂ → CPred} {E : Ξ}
    (h₁ : ⦃P⦄ a₁ ⊑[γ] c₁ ⦃fun av cv => ⌜av = f cv⌝; E⦄)
    (h₂ : ∀ cv, ⦃(⊤ : CPred)⦄ (a₂ (f cv)) ⊑[γ] (c₂ cv) ⦃Q; E⦄) :
    ⦃P⦄ (a₁ >>= a₂) ⊑[γ] (c₁ >>= c₂) ⦃Q; E⦄ :=
  .bind' h₁ fun av cv => .of_prop fun h => by rw [h]; exact h₂ cv

/-- The erased-leaf bind: a concrete head abstracted by `pure v` leaves no abstract bind; the
mid-coupling it establishes is threaded to the continuation. -/
theorem RTriple.bind_erase [Frame CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
    {v : AV} {c₁ : CM CV} {a : AM AV₂} {c₂ : CV → CM CV₂}
    {R : CV → CPred} {Q : AV₂ → CV₂ → CPred} {E : Ξ}
    (h₁ : ⦃P⦄ (Pure.pure v : AM AV) ⊑[γ] c₁ ⦃fun _ cv => R cv; E⦄)
    (h₂ : ∀ cv, ⦃R cv⦄ a ⊑[γ] (c₂ cv) ⦃Q; E⦄) :
    ⦃P⦄ a ⊑[γ] (c₁ >>= c₂) ⦃Q; E⦄ := by
  have h := RTriple.bind' (a₂ := fun _ => a) h₁ fun av cv => h₂ cv
  simpa only [pure_bind] using h

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
  [Frame BPred] [Frame CPred]

/-- Refinements at functional couplings compose through the composed concretization: the outer
`pred` transports the middle refinement, `hE` aligns the barrel transports (definitional on
delegating shapes). The middle refinement holds unconditionally; a middle-lattice precondition
has no transport into the concrete lattice. -/
theorem RTriple.comp
    {γ₁ : Concretization CPred BPred CEPred BEPred}
    {γ₂ : Concretization BPred APred BEPred AEPred}
    {f₁ : CVal → BVal} {f₂ : BVal → AVal} {E₁ : Ξ₁} {E₂ : Ξ₂} {E : Ξ} {P : CPred}
    {a : AProg} {b : BProg} {c : CProg}
    (hE : ∀ Ea, γ₁.ePost E₁ (γ₂.ePost E₂ Ea) = (γ₁.comp γ₂).ePost E Ea)
    (h₂ : ⦃(⊤ : BPred)⦄ a ⊑[γ₂] b ⦃fun av bv => ⌜av = f₂ bv⌝; E₂⦄)
    (h₁ : ⦃P⦄ b ⊑[γ₁] c ⦃fun bv cv => ⌜bv = f₁ cv⌝; E₁⦄) :
    ⦃P⦄ a ⊑[γ₁.comp γ₂] c ⦃fun av cv => ⌜av = f₂ (f₁ cv)⌝; E⦄ := by
  refine RTriple.intro fun Qa Ea => ?_
  have hb : γ₂.pred (wp a Qa Ea) ⊑
      wp b (γ₂.post (fun av bv => ⌜av = f₂ bv⌝) Qa) (γ₂.ePost E₂ Ea) := by
    have h := h₂.elim Qa Ea
    rwa [CompleteLattice.top_meet] at h
  have hc := h₁.elim (γ₂.post (fun av bv => ⌜av = f₂ bv⌝) Qa) (γ₂.ePost E₂ Ea)
  rw [hE Ea] at hc
  refine PartialOrder.rel_trans
    (le_meet _ _ _ (meet_le_left _ _)
      (PartialOrder.rel_trans (meet_le_right _ _) (γ₁.pred_mono hb))) ?_
  refine PartialOrder.rel_trans hc ?_
  refine WP.wp_consequence c _ _ _ fun cv => ?_
  simp only [Concretization.post_eq, Concretization.comp, Function.comp]
  exact PartialOrder.rel_refl

end Comp

/-! ## Purification: dropping the state monad -/

/-- A write-once concrete program (its result `v` and final state `w` are independent of the
initial state) is abstracted by the pure return of its result and final state; the terminal
coupling `purifyCouple` reads the exit state into the value. -/
theorem RTriple.purify {CProg σ α : Type} [WP CProg α (σ → Prop) EPost.Nil]
    (c : CProg) (v : α) (w : σ)
    (hc : ∀ (Q : α → σ → Prop) (E : EPost.Nil), (fun _ => Q v w) ⊑ wp c Q E) :
    ⦃(⊤ : σ → Prop)⦄ (Pure.pure (v, w) : Id (α × σ)) ⊑[Ascent.purify σ] c ⦃purifyCouple⦄ := by
  refine RTriple.intro fun Qa Ea => ?_
  rw [purify_post]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  refine PartialOrder.rel_trans ?_ (hc (fun cv s => Qa (cv, s)) _)
  exact le_of_forall_le fun s => PartialOrder.rel_refl


section
variable {εa εc AV CV : Type}
  {γ : Concretization Prop Prop (EPost.Cons (εc → Prop) EPost.Nil)
    (EPost.Cons (εa → Prop) EPost.Nil)}

/-- The relational throw law: `throw` consumes the relational exceptional postcondition,
exactly as `pure` consumes the relational postcondition. -/
theorem rwp_throw {Q : AV → CV → Prop} {E : εa → εc → Prop} (ea : εa) (ec : εc) :
    E ea ec ⊑
      rwp γ (MonadExceptOf.throw ea : Except εa AV)
        (MonadExceptOf.throw ec : Except εc CV) Q E := by
  refine RTriple.intro fun Qa Ea => ?_
  simp only [WPMonad.wp_throw_Except_apply_eq, Concretization.ePost_cons_head]
  exact CompleteLattice.le_iSup_of_le ea PartialOrder.rel_refl

/-- The relational tryCatch law: `tryCatch` rebinds the relational exceptional postcondition
with the handlers' `rwp`, exactly as `bind` rebinds the relational postcondition; the
relational postcondition threads. -/
theorem rwp_tryCatch {Q : AV → CV → Prop} {E : εa → εc → Prop}
    {ax : Except εa AV} {cx : Except εc CV}
    {ah : εa → Except εa AV} {ch : εc → Except εc CV} :
    rwp γ ax cx Q (fun ea ec => rwp γ (ah ea) (ch ec) Q E) ⊑
      rwp γ (MonadExceptOf.tryCatch ax ah) (MonadExceptOf.tryCatch cx ch) Q E := by
  refine RTriple.intro fun Qa Ea => ?_
  simp only [WPMonad.wp_tryCatch_Except_apply_eq]
  refine PartialOrder.rel_trans
    (CompleteLattice.meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ Qa)
        (iInf_le _ (epost⟨fun ea => wp (ah ea) Qa Ea⟩)))) ?_
  refine WP.wp_consequence_econs cx _ _ _ _ PartialOrder.rel_refl ?_
  refine EPost.Cons.mk_le _ _ _ ?_ PartialOrder.rel_refl
  intro ec
  show iSup (fun ea => rwp γ (ah ea) (ch ec) Q E ⊓ γ.pred (wp (ah ea) Qa Ea)) ⊑ _
  refine iSup_le _ _ fun ea => ?_
  exact CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))

end

section
variable {εa εc AV CV : Type}
  {γ : Concretization Prop Prop (EPost.Cons (εc → Prop) EPost.Nil)
    (EPost.Cons (εa → Prop) EPost.Nil)}

/-- The triple throw rule: `throw` consumes the exception coupling. -/
theorem RTriple.throw {Q : AV → CV → Prop} {E : εa → εc → Prop} (ea : εa) (ec : εc) :
    ⦃E ea ec⦄ (MonadExceptOf.throw ea : Except εa AV)
      ⊑[γ] (MonadExceptOf.throw ec : Except εc CV) ⦃Q; E⦄ :=
  rwp_throw ea ec

/-- The triple tryCatch rule, post-parametric form: the body's exception coupling is the
handlers' `rwp`. -/
theorem RTriple.tryCatch {P : Prop} {Q : AV → CV → Prop} {E : εa → εc → Prop}
    {ax : Except εa AV} {cx : Except εc CV}
    {ah : εa → Except εa AV} {ch : εc → Except εc CV}
    (h : ⦃P⦄ ax ⊑[γ] cx ⦃Q; fun ea ec => rwp γ (ah ea) (ch ec) Q E⦄) :
    ⦃P⦄ (MonadExceptOf.tryCatch ax ah) ⊑[γ] (MonadExceptOf.tryCatch cx ch) ⦃Q; E⦄ :=
  PartialOrder.rel_trans h rwp_tryCatch

end

end Ascent
