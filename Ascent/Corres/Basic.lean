import Std.WP
import Ascent.WPMonadExact

/-!
# `Concretization`: monad-level abstraction of assertions

`Concretization` carries the monad-level concretizations `pred`/`ePred` (the AutoCorres
state/exception abstraction; `Concretization.ofStateRepr` builds the common functional case as a
pullback). The value-level coupling is a relational postcondition supplied per refinement triple
(`Ascent.Corres.Refinement`); `Concretization.post` reifies it against an abstract postcondition.
-/

open Std.WP Lean.Order

namespace Ascent

universe u v w w'

/-- Monad-level concretizations of normal and exceptional assertions, mapping an abstract `WP`
setup's predicates into a concrete one's. The value-level coupling is supplied per refinement
triple. -/
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

/-- Postcondition concretization. The value coupling `couple cv av : CPred` relates a concrete
value `cv` to an abstract value `av`; being a `CPred`, it may depend on the concrete state, which
is what lets an out-parameter's final value be read off the exit state. For each concrete value
the abstract postcondition is reified against the coupling and concretized. -/
noncomputable def post (r : Concretization CPred APred CEPred AEPred) {CVal AVal : Type _}
    (couple : CVal → AVal → CPred) (Q : AVal → APred) : CVal → CPred :=
  fun cv => iSup fun av => couple cv av ⊓ r.pred (Q av)

/-- One-point rule: under a functional coupling `⌜f · = ·⌝` the reified `iSup` collapses to the
pullback. -/
@[simp] theorem post_eq (r : Concretization CPred APred CEPred AEPred) {CVal AVal : Type _}
    (f : CVal → AVal) (Q : AVal → APred) :
    r.post (fun cv av => (⌜f cv = av⌝ : CPred)) Q = fun cv => r.pred (Q (f cv)) := by
  funext cv
  refine PartialOrder.rel_antisymm (iSup_le _ _ fun av => ?_) ?_
  · exact CompleteLattice.ofProp_meet_le (by rintro rfl; exact PartialOrder.rel_refl)
  · refine PartialOrder.rel_trans ?_
      (le_iSup (fun av => (⌜f cv = av⌝ : CPred) ⊓ r.pred (Q av)) (f cv))
    exact le_meet _ _ _ (CompleteLattice.le_ofProp _ _ rfl) PartialOrder.rel_refl

/-- `post` in the `Prop` lattice, elementwise: some abstract value is coupled and satisfies the
concretized postcondition. -/
theorem post_prop {APred : Type} {CEPred AEPred : Type w'}
    [Assertion APred] [Assertion CEPred] [Assertion AEPred]
    (r : Concretization Prop APred CEPred AEPred) {CVal AVal : Type _}
    (couple : CVal → AVal → Prop) (Q : AVal → APred) (cv : CVal) :
    r.post couple Q cv = ∃ av, couple cv av ∧ r.pred (Q av) := by
  simp only [Concretization.post, iSup_prop_eq_exists, meet_prop_eq_and]

/-- `post` in a function lattice into `Prop`, elementwise. -/
theorem post_pi {σ : Type} {APred : Type} {CEPred AEPred : Type w'}
    [Assertion APred] [Assertion CEPred] [Assertion AEPred]
    (r : Concretization (σ → Prop) APred CEPred AEPred) {CVal AVal : Type _}
    (couple : CVal → AVal → σ → Prop) (Q : AVal → APred) (cv : CVal) (s : σ) :
    r.post couple Q cv s = ∃ av, couple cv av s ∧ r.pred (Q av) s := by
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
    meet_prop_eq_and]

/-- The functional concretization from a state representation function `st : Cσ → Aσ`: the
concretization is the pullback `st^*` (`pred P = P ∘ st`). Exception-free (`EStack⟨⟩`). This is
AutoCorres' functional state abstraction; the coupling side-condition lives in the `Corres`
precondition `pre`, not here. -/
def ofStateRepr {Cσ Aσ : Type w} (st : Cσ → Aσ) :
    Concretization (Cσ → Prop) (Aσ → Prop) EStack⟨⟩ EStack⟨⟩ where
  pred P := fun cs => P (st cs)
  ePred := id
  pred_mono h := fun cs => h (st cs)
  ePred_mono h := h

@[simp] theorem ofStateRepr_pred {Cσ Aσ : Type w} (st : Cσ → Aσ) (P : Aσ → Prop) :
    (ofStateRepr st).pred P = fun cs => P (st cs) := rfl

end Concretization

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

end Id

/-! ## Purification: dropping the state monad

An out-parameter is modelled as concrete *state*. When the concrete program is write-once (its
result and final state do not depend on the initial state), that state can be read off the exit and
returned as a pure *value*, eliminating the state monad. This is the terminal value coupling that
the state-aware `couple` was introduced for: `purifyCouple cv av s := ⌜av = (cv, s)⌝` reads the entire
final state into the second component of the abstract result. It is sound only here, at the end of
the program, where there is no continuation whose control flow could depend on the read. -/

section Purify

/-- Drops an abstract `Id` assertion (a `Prop`) to a constant concrete-state predicate. The exit
read lives entirely in the value coupling `purifyCouple`. -/
noncomputable def purify (σ : Type) : Concretization (σ → Prop) Prop EStack⟨⟩ EStack⟨⟩ where
  pred φ := fun _ => φ
  ePred := id
  pred_mono h := fun _ => h
  ePred_mono h := h

/-- The terminal value coupling: `(cv, s)` abstracts a concrete return `cv` ending in state `s`. -/
def purifyCouple {σ α : Type} : α → (α × σ) → (σ → Prop) :=
  fun cv av s => av = (cv, s)

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

end Purify

end Ascent
