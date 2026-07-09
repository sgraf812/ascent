import Std.Internal.Do
import Ascent.WPMonadExact

/-!
# `Corres`: soundness of monadic abstraction

`Corres r b a c` states that, under the boundary `b`, the abstract program `a` soundly abstracts the
concrete program `c`: any property proved of `a` transports to `c` where `b.pre` holds. It is read as
abstract interpretation,
`(b.pre ⊓ r.pred (wp a Q E)) ⊑ wp c (r.post b.couple Q) (r.ePred E)`.

`Concretization` carries the monad-level concretizations `pred`/`ePred` (the AutoCorres state/exception
abstraction; `Concretization.ofStateRepr` builds the common functional case as a pullback). `Boundary`
carries the entry precondition `pre` and the exit value coupling `couple`; the coupling is per-`Corres`
(`bind` relates programs at different value types). The precondition is threaded by `corres_bind` (the
AutoCorres `corresXF_split`), so a coupling that is *established* mid-program (e.g. a loop counter) need
not hold from the start.
-/

open Std.Internal.Do Lean.Order

namespace Ascent

universe u v w w'

/-- Monad-level concretizations of normal and exceptional assertions, mapping an abstract `WP`
setup's predicates into a concrete one's. The value-level coupling is supplied per `Corres`
statement. -/
structure Concretization (CPred : Type w) (APred : Type w) (CEPred : Type w') (AEPred : Type w')
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred] where
  /-- Concretization of normal assertions. -/
  pred : APred → CPred
  /-- Concretization of exceptional assertions. -/
  ePred : AEPred → CEPred
  /-- `pred` is monotone. -/
  pred_mono : ∀ {p q : APred}, p ⊑ q → pred p ⊑ pred q
  /-- `ePred` is monotone. -/
  ePred_mono : ∀ {p q : AEPred}, p ⊑ q → ePred p ⊑ ePred q

namespace Concretization

variable {CPred APred : Type w} {CEPred AEPred : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]

/-- Postcondition concretization. The value coupling `couple av cv : CPred` relates an abstract value
`av` to a concrete value `cv`; being a `CPred`, it may depend on the concrete state, which is what
lets an out-parameter's final value be read off the exit state. For each concrete value the abstract
postcondition is reified against the coupling and concretized. -/
noncomputable def post (r : Concretization CPred APred CEPred AEPred) {CVal AVal : Type _}
    (couple : AVal → CVal → CPred) (Q : AVal → APred) : CVal → CPred :=
  fun cv => iSup fun av => couple av cv ⊓ r.pred (Q av)

end Concretization

/-- The functional value coupling: the abstract value is exactly `f cv`. Recovers the
state-independent value abstraction. -/
noncomputable def coupleEq {CVal AVal : Type _} {CPred : Type w} [Assertion CPred] (f : CVal → AVal) :
    AVal → CVal → CPred := fun av cv => ⌜av = f cv⌝

namespace Concretization

variable {CPred APred : Type w} {CEPred AEPred : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]

/-- One-point rule: under a functional coupling `⌜· = f ·⌝` the reified `iSup` collapses to the
pullback. -/
@[simp] theorem post_eq (r : Concretization CPred APred CEPred AEPred) {CVal AVal : Type _}
    (f : CVal → AVal) (Q : AVal → APred) :
    r.post (fun av cv => (⌜av = f cv⌝ : CPred)) Q = fun cv => r.pred (Q (f cv)) := by
  funext cv
  refine PartialOrder.rel_antisymm (iSup_le _ _ fun av => ?_) ?_
  · exact CompleteLattice.ofProp_meet_le_left (by rintro rfl; exact PartialOrder.rel_refl)
  · refine PartialOrder.rel_trans ?_
      (le_iSup (fun av => (⌜av = f cv⌝ : CPred) ⊓ r.pred (Q av)) (f cv))
    exact le_meet _ _ _ (le_ofProp _ _ rfl) PartialOrder.rel_refl

/-- One-point rule: under the functional coupling the reified `iSup` collapses to the pullback. -/
@[simp] theorem post_coupleEq (r : Concretization CPred APred CEPred AEPred) {CVal AVal : Type _}
    (f : CVal → AVal) (Q : AVal → APred) :
    r.post (coupleEq f) Q = fun cv => r.pred (Q (f cv)) :=
  r.post_eq f Q

/-- The functional concretization from a state representation function `st : Cσ → Aσ`: the
concretization is the pullback `st^*` (`pred P = P ∘ st`). Exception-free (`EPost.Nil`). This is
AutoCorres' functional state abstraction; the coupling side-condition lives in the `Corres`
precondition `pre`, not here. -/
def ofStateRepr {Cσ Aσ : Type w} (st : Cσ → Aσ) :
    Concretization (Cσ → Prop) (Aσ → Prop) EPost.Nil EPost.Nil where
  pred P := fun cs => P (st cs)
  ePred := id
  pred_mono h := fun cs => h (st cs)
  ePred_mono h := h

@[simp] theorem ofStateRepr_pred {Cσ Aσ : Type w} (st : Cσ → Aσ) (P : Aσ → Prop) :
    (ofStateRepr st).pred P = fun cs => P (st cs) := rfl

@[simp] theorem ofStateRepr_post {Cσ Aσ CV AV : Type w} (st : Cσ → Aσ) (f : CV → AV)
    (Q : AV → Aσ → Prop) : (ofStateRepr st).post (coupleEq f) Q = fun cv cs => Q (f cv) (st cs) := by
  simp only [post_coupleEq, ofStateRepr_pred]

end Concretization

/-- The boundary of a `Corres` statement: the concrete-state precondition assumed on entry, and the
value coupling relating the abstract and concrete return values on exit. -/
structure Boundary (CPred : Type w) (AVal CVal : Type _) where
  /-- Concrete-state precondition assumed on entry. -/
  pre : CPred
  /-- Value coupling relating an abstract and concrete return value on exit. -/
  couple : AVal → CVal → CPred

/-- The boundary whose coupling is the functional one (`couple = coupleEq f`). -/
@[reducible] noncomputable def Boundary.eq {CPred : Type w} {AVal CVal : Type _} [Assertion CPred]
    (pre : CPred) (f : CVal → AVal) : Boundary CPred AVal CVal := ⟨pre, coupleEq f⟩

/-- The trivial boundary: no precondition (`⊤`) and the identity value coupling. -/
@[reducible] noncomputable def Boundary.trivial {CPred : Type w} {Val : Type _} [Assertion CPred] :
    Boundary CPred Val Val := .eq ⊤ id

/-- The abstract program `a` soundly abstracts the concrete program `c` under concretization `r`
across the boundary `b` (entry precondition and exit value coupling). -/
def Corres {CProg AProg : Type _} {CVal AVal : Type _}
    {CPred APred : Type w} {CEPred AEPred : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
    [WP CProg CVal CPred CEPred] [WP AProg AVal APred AEPred]
    (r : Concretization CPred APred CEPred AEPred) (b : Boundary CPred AVal CVal)
    (a : AProg) (c : CProg) : Prop :=
  ∀ Q E, (b.pre ⊓ r.pred (wp a Q E)) ⊑ wp c (r.post b.couple Q) (r.ePred E)

/-! ## Structural laws -/

section Structural

variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPred AEPred : Type w'}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WPMonad CM CPred CEPred] [WPMonad AM APred AEPred] [WPMonadExact AM APred AEPred]

variable {r : Concretization CPred APred CEPred AEPred}

/-- `pure` abstracts `pure` when the returned values correspond (precondition-agnostic). -/
theorem corres_pure {CVal AVal : Type w} (pre : CPred) (couple : CVal → AVal) {a : AVal} {c : CVal}
    (h : couple c = a) : Corres r (.eq pre couple) (pure a : AM AVal) (pure c : CM CVal) := by
  intro Q E
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  refine PartialOrder.rel_trans (r.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_pure_le a Q E)) ?_
  have hQ : r.post (coupleEq couple) Q c = r.pred (Q a) := by simp [Concretization.post_coupleEq, h]
  rw [← hQ]
  exact WPMonad.pure_le_wp_pure c (r.post (coupleEq couple) Q) (r.ePred E)

/-- `bind` abstracts `bind`, threading the precondition (`corresXF_split`): the heads correspond
under `pre`, the concrete head establishes the mid-coupling `R` on normal return (the `⊥`
exception postcondition), and the continuations correspond under `R`. -/
theorem corres_bind {CV AV CV₂ AV₂ : Type w} [WPConjunctive (CM CV) CV CPred CEPred] (pre : CPred) (R : CV → CPred)
    (couple : CV → AV) (couple₂ : CV₂ → AV₂)
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    (hc : Corres r (.eq pre couple) a₁ c₁)
    (hmid : pre ⊑ wp c₁ (fun cv => R cv) ⊥)
    (hf : ∀ cv, Corres r (.eq (R cv) couple₂) (a₂ (couple cv)) (c₂ cv)) :
    Corres r (.eq pre couple₂) (a₁ >>= a₂) (c₁ >>= c₂) := by
  intro Q E
  have step1 : (pre ⊓ r.pred (wp (a₁ >>= a₂) Q E)) ⊑ (pre ⊓ r.pred (wp a₁ (fun av => wp (a₂ av) Q E) E)) :=
    le_meet _ _ _ (meet_le_left _ _)
      (PartialOrder.rel_trans (meet_le_right _ _) (r.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_bind_le a₁ a₂ Q E)))
  refine PartialOrder.rel_trans step1 ?_
  have hi := hc (fun av => wp (a₂ av) Q E) E
  have hii : (pre ⊓ r.pred (wp a₁ (fun av => wp (a₂ av) Q E) E)) ⊑ wp c₁ (fun cv => R cv) (r.ePred E) :=
    PartialOrder.rel_trans (meet_le_left _ _)
      (WP.wp_econs_bot_le c₁ (fun cv => R cv) (r.ePred E) hmid)
  refine PartialOrder.rel_trans (le_meet _ _ _ hi hii) ?_
  refine PartialOrder.rel_trans (WPConjunctive.wp_meet_wp_le c₁ (r.post (coupleEq couple) (fun av => wp (a₂ av) Q E))
    (fun cv => R cv) (r.ePred E)) ?_
  refine PartialOrder.rel_trans
    (WP.wp_consequence c₁ _ (fun cv => wp (c₂ cv) (r.post (coupleEq couple₂) Q) (r.ePred E)) (r.ePred E) ?_) ?_
  · intro cv
    simp only [Concretization.post_coupleEq, meet_apply]
    have hfcv := hf cv Q E
    simp only [Concretization.post_coupleEq] at hfcv
    refine PartialOrder.rel_trans ?_ hfcv
    exact le_meet _ _ _ (meet_le_right _ _) (meet_le_left _ _)
  · exact WPMonad.bind_le_wp_bind c₁ c₂ (r.post (coupleEq couple₂) Q) (r.ePred E)

/-- The precondition-free `bind`: when no mid-coupling is needed (`pre = ⊤`, `R = ⊤`), neither `hmid`
nor conjunctivity is used. -/
theorem corres_bind_top {CV AV CV₂ AV₂ : Type w} (couple : CV → AV) (couple₂ : CV₂ → AV₂)
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    (hc : Corres r (.eq ⊤ couple) a₁ c₁) (hf : ∀ cv, Corres r (.eq ⊤ couple₂) (a₂ (couple cv)) (c₂ cv)) :
    Corres r (.eq ⊤ couple₂) (a₁ >>= a₂) (c₁ >>= c₂) := by
  intro Q E
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  refine PartialOrder.rel_trans (r.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_bind_le a₁ a₂ Q E)) ?_
  have hi : r.pred (wp a₁ (fun av => wp (a₂ av) Q E) E) ⊑
      wp c₁ (r.post (coupleEq couple) (fun av => wp (a₂ av) Q E)) (r.ePred E) :=
    PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl)
      (hc (fun av => wp (a₂ av) Q E) E)
  refine PartialOrder.rel_trans hi ?_
  refine PartialOrder.rel_trans
    (WP.wp_consequence c₁ _ (fun cv => wp (c₂ cv) (r.post (coupleEq couple₂) Q) (r.ePred E)) (r.ePred E) ?_) ?_
  · intro cv
    simp only [Concretization.post_coupleEq]
    have hfcv := hf cv Q E
    simp only [Concretization.post_coupleEq] at hfcv
    exact PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl) hfcv
  · exact WPMonad.bind_le_wp_bind c₁ c₂ (r.post (coupleEq couple₂) Q) (r.ePred E)

/-- The erased-leaf `bind`: a concrete head abstracted by `pure v` leaves no abstract bind; its
effect survives as the mid-condition `R` threaded to the continuation. -/
theorem corres_bind_erase {CV AV CV₂ AV₂ : Type w} [WPConjunctive (CM CV) CV CPred CEPred]
    (pre : CPred) (R : CV → CPred) (couple : CV → AV) (couple₂ : CV₂ → AV₂)
    {v : AV} {c₁ : CM CV} {a : AM AV₂} {c₂ : CV → CM CV₂}
    (hc : Corres r (.eq pre couple) (pure v : AM AV) c₁)
    (hmid : pre ⊑ wp c₁ (fun cv => R cv) ⊥)
    (hf : ∀ cv, Corres r (.eq (R cv) couple₂) a (c₂ cv)) :
    Corres r (.eq pre couple₂) a (c₁ >>= c₂) := by
  have h := corres_bind pre R couple couple₂ (a₂ := fun _ => a) hc hmid hf
  simpa only [pure_bind] using h

omit [WPMonadExact AM APred AEPred] in
/-- Branch congruence on a shared condition. -/
theorem corres_ite (r : Concretization CPred APred CEPred AEPred) {CVal AVal : Type w}
    (b : Boundary CPred AVal CVal) {cond : Prop} [Decidable cond]
    {a₁ a₂ : AM AVal} {c₁ c₂ : CM CVal}
    (h₁ : Corres r b a₁ c₁) (h₂ : Corres r b a₂ c₂) :
    Corres r b (if cond then a₁ else a₂) (if cond then c₁ else c₂) := by
  by_cases hc : cond <;> simp only [hc, if_true, if_false] <;> assumption

end Structural

/-! ## Composition of refinements -/

section Comp

variable {CPred BPred APred : Type w} {CEPred BEPred AEPred : Type w'}
  [Assertion CPred] [Assertion BPred] [Assertion APred]
  [Assertion CEPred] [Assertion BEPred] [Assertion AEPred]

/-- Compose refinements `C ← B` and `B ← A` into `C ← A`. -/
def Concretization.comp (r₁ : Concretization CPred BPred CEPred BEPred)
    (r₂ : Concretization BPred APred BEPred AEPred) : Concretization CPred APred CEPred AEPred where
  pred := r₁.pred ∘ r₂.pred
  ePred := r₁.ePred ∘ r₂.ePred
  pred_mono h := r₁.pred_mono (r₂.pred_mono h)
  ePred_mono h := r₁.ePred_mono (r₂.ePred_mono h)

/-- Correspondence composes (preconditions `⊤`): composing the refinements and value couplings. -/
theorem corres_comp {CProg BProg AProg : Type _} {CVal BVal AVal : Type _}
    [WP CProg CVal CPred CEPred] [WP BProg BVal BPred BEPred] [WP AProg AVal APred AEPred]
    {r₁ : Concretization CPred BPred CEPred BEPred} {r₂ : Concretization BPred APred BEPred AEPred}
    {couple₁ : CVal → BVal} {couple₂ : BVal → AVal} {a : AProg} {b : BProg} {c : CProg}
    (hc : Corres r₁ (.eq ⊤ couple₁) b c) (hb : Corres r₂ (.eq ⊤ couple₂) a b) :
    Corres (r₁.comp r₂) (.eq ⊤ (couple₂ ∘ couple₁)) a c := by
  intro Q E
  have hpost : (r₁.comp r₂).post (coupleEq (couple₂ ∘ couple₁)) Q = r₁.post (coupleEq couple₁) (r₂.post (coupleEq couple₂) Q) := by
    simp only [Concretization.post_coupleEq, Concretization.comp, Function.comp]
  rw [hpost]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  have hb' : r₂.pred (wp a Q E) ⊑ wp b (r₂.post (coupleEq couple₂) Q) (r₂.ePred E) :=
    PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl) (hb Q E)
  have hc' := hc (r₂.post (coupleEq couple₂) Q) (r₂.ePred E)
  exact PartialOrder.rel_trans (r₁.pred_mono hb')
    (PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl) hc')

/-- Correspondence (precondition `⊤`) chains in `calc`/`Trans`. -/
instance {CProg BProg AProg : Type _} {CVal BVal AVal : Type _}
    [WP CProg CVal CPred CEPred] [WP BProg BVal BPred BEPred] [WP AProg AVal APred AEPred]
    {r₁ : Concretization CPred BPred CEPred BEPred} {r₂ : Concretization BPred APred BEPred AEPred}
    {couple₁ : CVal → BVal} {couple₂ : BVal → AVal} :
    Trans (Corres r₂ (.eq ⊤ couple₂) : AProg → BProg → Prop)
      (Corres r₁ (.eq ⊤ couple₁) : BProg → CProg → Prop)
      (Corres (r₁.comp r₂) (.eq ⊤ (couple₂ ∘ couple₁)) : AProg → CProg → Prop) where
  trans hab hbc := corres_comp hbc hab

end Comp

/-! ## Identity concretization -/

section Id

variable {Pred : Type w} {EPred : Type w'} [Assertion Pred] [Assertion EPred]

/-- The concretization that is the identity on both assertion lattices. -/
def Concretization.id (Pred : Type w) (EPred : Type w') [Assertion Pred] [Assertion EPred] :
    Concretization Pred Pred EPred EPred where
  pred := _root_.id
  ePred := _root_.id
  pred_mono h := h
  ePred_mono h := h

/-- Every program abstracts itself under the identity concretization, for any precondition. -/
theorem corres_id {Prog Val : Type _} [WP Prog Val Pred EPred] (pre : Pred) (x : Prog) :
    Corres (Concretization.id Pred EPred) (.eq pre (id : Val → Val)) x x := by
  intro Q E
  have hpost : (Concretization.id Pred EPred).post (coupleEq id) Q = Q := by
    funext cv; simp only [Concretization.post_coupleEq, Concretization.id, id_eq]
  rw [hpost]
  exact meet_le_right _ _

end Id

/-! ## Purification: dropping the state monad

An out-parameter is modelled as concrete *state*. When the concrete program is write-once (its
result and final state do not depend on the initial state), that state can be read off the exit and
returned as a pure *value*, eliminating the state monad. This is the terminal value coupling that
the state-aware `couple` was introduced for: `purifyCouple av cv s := ⌜av = (cv, s)⌝` reads the entire
final state into the second component of the abstract result. It is sound only here, at the end of
the program, where there is no continuation whose control flow could depend on the read. -/

section Purify

/-- Drops an abstract `Id` assertion (a `Prop`) to a constant concrete-state predicate. The exit
read lives entirely in the value coupling `purifyCouple`. -/
noncomputable def purify (σ : Type) : Concretization (σ → Prop) Prop EPost.Nil EPost.Nil where
  pred φ := fun _ => φ
  ePred := id
  pred_mono h := fun _ => h
  ePred_mono h := h

/-- The terminal value coupling: `(cv, s)` abstracts a concrete return `cv` ending in state `s`. -/
def purifyCouple {σ α : Type} : (α × σ) → α → (σ → Prop) :=
  fun av cv s => av = (cv, s)

/-- Under `purifyCouple`, the postcondition concretization reads the final state into the result. -/
@[simp] theorem purify_post {σ α : Type} (Q : (α × σ) → Prop) :
    (purify σ).post purifyCouple Q = fun cv s => Q (cv, s) := by
  funext cv s
  simp only [Concretization.post, purify, purifyCouple, iSup_apply, meet_apply, iSup_prop_eq_exists,
    meet_prop_eq_and]
  apply propext
  constructor
  · rintro ⟨i, rfl, h⟩; exact h
  · intro h; exact ⟨(cv, s), rfl, h⟩

/-- A write-once concrete program (its result `v` and final state `w` are independent of the initial
state) is abstracted by the pure return of its result-and-final-state, with no state monad. -/
theorem corres_purify {CProg σ α : Type} [WP CProg α (σ → Prop) EPost.Nil]
    (c : CProg) (v : α) (w : σ)
    (hc : ∀ (Q : α → σ → Prop) (E : EPost.Nil), (fun _ => Q v w) ⊑ wp c Q E) :
    Corres (purify σ) ⟨⊤, purifyCouple⟩ (pure (v, w) : Id (α × σ)) c := by
  intro Q E
  rw [purify_post]
  refine PartialOrder.rel_trans (PartialOrder.rel_trans (meet_le_right _ _) ?_)
    (hc (fun cv s => Q (cv, s)) E)
  apply le_of_forall_le
  intro s
  exact PartialOrder.rel_refl

end Purify

end Ascent
