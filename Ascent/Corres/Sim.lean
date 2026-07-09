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
instance {CPred APred εh CRest : Type} [Assertion CPred] [Assertion APred] [Assertion εh]
    [Assertion CRest] :
    HasEPost CPred APred (EPost.Cons εh CRest) EPost.Nil Unit where
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

@[simp] theorem Concretization.ePost_fill {CPred APred εh CRest : Type}
    [Assertion CPred] [Assertion APred] [Assertion εh] [Assertion CRest]
    (γ : Concretization CPred APred (EPost.Cons εh CRest) EPost.Nil)
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

variable {γ : Concretization CPred APred CEPred AEPred} {P : CPred}
  {a : AProg} {c : CProg} {Q : AVal → CVal → CPred} {E : Ξ}

/-- Weaken the precondition. -/
theorem SimTriple.weaken {P' : CPred}
    (h : ⦃P⦄ a ⊑[γ] c ⦃Q; E⦄) (hP : P' ⊑ P) : ⦃P'⦄ a ⊑[γ] c ⦃Q; E⦄ :=
  PartialOrder.rel_trans hP h

/-- Introduction, unfolded: a simulation triple transports each abstract `wp` fact under the
precondition. -/
theorem SimTriple.intro
    (h : ∀ (Qa : AVal → APred) (Ea : AEPred),
      P ⊓ γ.pred (wp a Qa Ea) ⊑ wp c (γ.post Q Qa) (γ.ePost E Ea)) :
    ⦃P⦄ a ⊑[γ] c ⦃Q; E⦄ :=
  le_iInf _ _ fun Qa => le_iInf _ _ fun Ea =>
    himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm (h Qa Ea))

/-- Elimination, unfolded: instantiate a simulation triple at an abstract postcondition pair. -/
theorem SimTriple.elim [Frame CPred] (h : ⦃P⦄ a ⊑[γ] c ⦃Q; E⦄)
    (Qa : AVal → APred) (Ea : AEPred) :
    P ⊓ γ.pred (wp a Qa Ea) ⊑ wp c (γ.post Q Qa) (γ.ePost E Ea) :=
  CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans h (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea)))

/-- `sim` is monotone in the value coupling. -/
theorem sim_mono_post [Frame CPred] {Q' : AVal → CVal → CPred}
    (hQ : ∀ av cv, Q av cv ⊑ Q' av cv) : sim γ a c Q E ⊑ sim γ a c Q' E := by
  refine CompleteLattice.iInf_mono fun Qa => CompleteLattice.iInf_mono fun Ea => ?_
  refine CompleteLattice.himp_mono PartialOrder.rel_refl ?_
  refine WP.wp_consequence c _ _ _ ?_
  intro cv
  refine iSup_le _ _ fun av => ?_
  exact PartialOrder.rel_trans
    (le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) (hQ av cv)) (meet_le_right _ _))
    (le_iSup (fun av' => Q' av' cv ⊓ γ.pred (Qa av')) av)

/-- Weaken the value coupling. -/
theorem SimTriple.mono_post [Frame CPred] {Q' : AVal → CVal → CPred}
    (h : ⦃P⦄ a ⊑[γ] c ⦃Q; E⦄) (hQ : ∀ av cv, Q av cv ⊑ Q' av cv) : ⦃P⦄ a ⊑[γ] c ⦃Q'; E⦄ :=
  PartialOrder.rel_trans h (sim_mono_post hQ)

/-- Consume a propositional precondition. -/
theorem SimTriple.of_prop {p : Prop} (h : p → ⦃(⊤ : CPred)⦄ a ⊑[γ] c ⦃Q; E⦄) :
    ⦃(⌜p⌝ : CPred)⦄ a ⊑[γ] c ⦃Q; E⦄ :=
  ofProp_le _ _ h

/-- Branch congruence on a shared condition. -/
theorem SimTriple.ite {cond : Prop} [Decidable cond] {a₁ a₂ : AProg} {c₁ c₂ : CProg}
    (h₁ : ⦃P⦄ a₁ ⊑[γ] c₁ ⦃Q; E⦄) (h₂ : ⦃P⦄ a₂ ⊑[γ] c₂ ⦃Q; E⦄) :
    ⦃P⦄ (if cond then a₁ else a₂) ⊑[γ] (if cond then c₁ else c₂) ⦃Q; E⦄ := by
  by_cases hc : cond <;> simp only [hc, if_true, if_false] <;> assumption

/-- A concrete `wp` fact rides along in the value coupling: what the concrete program
establishes on normal return strengthens the relational postcondition. -/
theorem SimTriple.conj_wp [Frame CPred] [WPConjunctive CProg CVal CPred CEPred]
    {R : CVal → CPred} (h : ⦃P⦄ a ⊑[γ] c ⦃Q; E⦄) (hw : P ⊑ wp c R ⊥) :
    ⦃P⦄ a ⊑[γ] c ⦃fun av cv => Q av cv ⊓ R cv; E⦄ := by
  refine SimTriple.intro fun Qa Ea => ?_
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

/-- The triple unit rule at a functional coupling. -/
theorem SimTriple.pure_coupleEq {AV CV : Type w} {f : CV → AV} {E : Ξ}
    (P : CPred) {av : AV} (cv : CV) (h : f cv = av) :
    ⦃P⦄ (Pure.pure av : AM AV) ⊑[γ] (Pure.pure cv : CM CV) ⦃coupleEq f; E⦄ :=
  (SimTriple.pure av cv).weaken (le_ofProp _ _ h.symm)

/-- The triple bind rule at a functional head coupling: the continuations correspond at each
concrete value and its coupled abstract value. -/
theorem SimTriple.bind_eq [Frame CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
    {f : CV → AV} {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {Q : AV₂ → CV₂ → CPred} {E : Ξ}
    (h₁ : ⦃P⦄ a₁ ⊑[γ] c₁ ⦃coupleEq f; E⦄)
    (h₂ : ∀ cv, ⦃(⊤ : CPred)⦄ (a₂ (f cv)) ⊑[γ] (c₂ cv) ⦃Q; E⦄) :
    ⦃P⦄ (a₁ >>= a₂) ⊑[γ] (c₁ >>= c₂) ⦃Q; E⦄ :=
  .bind' h₁ fun av cv => .of_prop fun h => by rw [h]; exact h₂ cv

/-- The erased-leaf bind: a concrete head abstracted by `pure v` leaves no abstract bind; the
mid-coupling it establishes is threaded to the continuation. -/
theorem SimTriple.bind_erase [Frame CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
    {v : AV} {c₁ : CM CV} {a : AM AV₂} {c₂ : CV → CM CV₂}
    {R : CV → CPred} {Q : AV₂ → CV₂ → CPred} {E : Ξ}
    (h₁ : ⦃P⦄ (Pure.pure v : AM AV) ⊑[γ] c₁ ⦃fun _ cv => R cv; E⦄)
    (h₂ : ∀ cv, ⦃R cv⦄ a ⊑[γ] (c₂ cv) ⦃Q; E⦄) :
    ⦃P⦄ a ⊑[γ] (c₁ >>= c₂) ⦃Q; E⦄ := by
  have h := SimTriple.bind' (a₂ := fun _ => a) h₁ fun av cv => h₂ cv
  simpa only [pure_bind] using h

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

/-! ## Composition of simulations -/

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

/-- Simulations at functional couplings compose through the composed concretization: the outer
`pred` transports the middle simulation, `hE` aligns the barrel transports (definitional on
delegating shapes). The middle simulation holds unconditionally; a middle-lattice precondition
has no transport into the concrete lattice. -/
theorem SimTriple.comp
    {γ₁ : Concretization CPred BPred CEPred BEPred}
    {γ₂ : Concretization BPred APred BEPred AEPred}
    {f₁ : CVal → BVal} {f₂ : BVal → AVal} {E₁ : Ξ₁} {E₂ : Ξ₂} {E : Ξ} {P : CPred}
    {a : AProg} {b : BProg} {c : CProg}
    (hE : ∀ Ea, γ₁.ePost E₁ (γ₂.ePost E₂ Ea) = (γ₁.comp γ₂).ePost E Ea)
    (h₂ : ⦃(⊤ : BPred)⦄ a ⊑[γ₂] b ⦃coupleEq f₂; E₂⦄)
    (h₁ : ⦃P⦄ b ⊑[γ₁] c ⦃coupleEq f₁; E₁⦄) :
    ⦃P⦄ a ⊑[γ₁.comp γ₂] c ⦃coupleEq (f₂ ∘ f₁); E⦄ := by
  refine SimTriple.intro fun Qa Ea => ?_
  have hb : γ₂.pred (wp a Qa Ea) ⊑ wp b (γ₂.post (coupleEq f₂) Qa) (γ₂.ePost E₂ Ea) := by
    have h := h₂.elim Qa Ea
    rwa [CompleteLattice.top_meet] at h
  have hc := h₁.elim (γ₂.post (coupleEq f₂) Qa) (γ₂.ePost E₂ Ea)
  rw [hE Ea] at hc
  refine PartialOrder.rel_trans
    (le_meet _ _ _ (meet_le_left _ _)
      (PartialOrder.rel_trans (meet_le_right _ _) (γ₁.pred_mono hb))) ?_
  refine PartialOrder.rel_trans hc ?_
  refine WP.wp_consequence c _ _ _ fun cv => ?_
  simp only [Concretization.post_coupleEq, Concretization.comp, Function.comp]
  exact PartialOrder.rel_refl

/-- Simulation at `⊤` precondition and functional couplings chains in `calc`. -/
instance {γ₁ : Concretization CPred BPred EPost.Nil EPost.Nil}
    {γ₂ : Concretization BPred APred EPost.Nil EPost.Nil}
    {f₁ : CVal → BVal} {f₂ : BVal → AVal}
    [WP CProg CVal CPred EPost.Nil] [WP BProg BVal BPred EPost.Nil]
    [WP AProg AVal APred EPost.Nil] :
    Trans (fun (a : AProg) (b : BProg) => ⦃(⊤ : BPred)⦄ a ⊑[γ₂] b ⦃coupleEq f₂; ()⦄)
      (fun (b : BProg) (c : CProg) => ⦃(⊤ : CPred)⦄ b ⊑[γ₁] c ⦃coupleEq f₁; ()⦄)
      (fun (a : AProg) (c : CProg) =>
        ⦃(⊤ : CPred)⦄ a ⊑[γ₁.comp γ₂] c ⦃coupleEq (f₂ ∘ f₁); ()⦄) where
  trans h₂ h₁ := SimTriple.comp (fun _ => rfl) h₂ h₁

end Comp

/-! ## The identity concretization -/

/-- Every program simulates itself under the identity concretization. -/
theorem SimTriple.refl {Prog Val : Type _} {Pred : Type w} [Assertion Pred]
    [WP Prog Val Pred EPost.Nil] (P : Pred) (x : Prog) :
    ⦃P⦄ x ⊑[Concretization.id Pred EPost.Nil] x ⦃coupleEq id; ()⦄ := by
  refine SimTriple.intro fun Qa Ea => ?_
  have hpost : (Concretization.id Pred EPost.Nil).post (coupleEq id) Qa = Qa := by
    funext cv; simp only [Concretization.post_coupleEq, Concretization.id, id_eq]
  rw [Concretization.ePost_nil, hpost]
  show P ⊓ wp x Qa Ea ⊑ wp x Qa Ea
  exact meet_le_right _ _

/-! ## Purification: dropping the state monad -/

/-- A write-once concrete program (its result `v` and final state `w` are independent of the
initial state) is abstracted by the pure return of its result and final state; the terminal
coupling `purifyCouple` reads the exit state into the value. -/
theorem SimTriple.purify {CProg σ α : Type} [WP CProg α (σ → Prop) EPost.Nil]
    (c : CProg) (v : α) (w : σ)
    (hc : ∀ (Q : α → σ → Prop) (E : EPost.Nil), (fun _ => Q v w) ⊑ wp c Q E) :
    ⦃(⊤ : σ → Prop)⦄ (Pure.pure (v, w) : Id (α × σ)) ⊑[Ascent.purify σ] c ⦃purifyCouple; ()⦄ := by
  refine SimTriple.intro fun Qa Ea => ?_
  rw [purify_post]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  refine PartialOrder.rel_trans ?_ (hc (fun cv s => Qa (cv, s)) _)
  exact le_of_forall_le fun s => PartialOrder.rel_refl

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
