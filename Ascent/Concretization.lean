import Std.WP
import Ascent.WPMonadExact

/-!
# Concretization

A `Concretization CPred APred` is a monotone map `pred : APred → CPred` from abstract assertions
to concrete assertions.

Example. `ofStateRepr st` for `st : Cσ → Aσ` has `pred P cs = P (st cs)`. Under it the abstract
assertion `fun as => as.1 < 10` becomes `fun cs => (st cs).1 < 10`.

`post` extends `pred` to postconditions on values. For a coupling `Q : CVal → AVal → CPred` and
an abstract postcondition `Qa : AVal → APred`, `post Q Qa cv = ⨆ av, Q cv av ⊓ pred (Qa av)`:
some abstract value is coupled to `cv` and satisfies `Qa`. For a functional coupling
`⌜f cv = av⌝` this is `pred (Qa (f cv))` (`post_eq`).
-/

open Std.WP Lean.Order

namespace Ascent

universe u v w

/-- A monotone map from abstract assertions to concrete assertions. -/
structure Concretization (CPred : Type w) (APred : Type w) [Assertion CPred] [Assertion APred] where
  /-- The concrete assertion for an abstract assertion. -/
  pred : APred → CPred
  /-- `pred` is monotone. -/
  pred_mono : ∀ {p q : APred}, p ⊑ q → pred p ⊑ pred q

namespace Concretization

variable {CPred APred : Type w} [Assertion CPred] [Assertion APred]

/-- The concrete postcondition for the coupling `couple` and the abstract postcondition `Q`:
`post couple Q cv = ⨆ av, couple cv av ⊓ pred (Q av)`. -/
noncomputable def post (r : Concretization CPred APred) {CVal AVal : Type _}
    (couple : CVal → AVal → CPred) (Q : AVal → APred) : CVal → CPred :=
  fun cv => iSup fun av => couple cv av ⊓ r.pred (Q av)

@[simp] theorem post_eq (r : Concretization CPred APred) {CVal AVal : Type _}
    (f : CVal → AVal) (Q : AVal → APred) :
    r.post (fun cv av => (⌜f cv = av⌝ : CPred)) Q = fun cv => r.pred (Q (f cv)) := by
  funext cv
  refine PartialOrder.rel_antisymm (iSup_le _ _ fun av => ?_) ?_
  · exact CompleteLattice.ofProp_meet_le (by rintro rfl; exact PartialOrder.rel_refl)
  · refine PartialOrder.rel_trans ?_
      (le_iSup (fun av => (⌜f cv = av⌝ : CPred) ⊓ r.pred (Q av)) (f cv))
    exact le_meet _ _ _ (CompleteLattice.le_ofProp _ _ rfl) PartialOrder.rel_refl

theorem post_prop {APred : Type} [Assertion APred]
    (r : Concretization Prop APred) {CVal AVal : Type _}
    (couple : CVal → AVal → Prop) (Q : AVal → APred) (cv : CVal) :
    r.post couple Q cv = ∃ av, couple cv av ∧ r.pred (Q av) := by
  simp only [Concretization.post, iSup_prop_eq_exists, meet_prop_eq_and]

theorem post_pi {σ : Type} {APred : Type} [Assertion APred]
    (r : Concretization (σ → Prop) APred) {CVal AVal : Type _}
    (couple : CVal → AVal → σ → Prop) (Q : AVal → APred) (cv : CVal) (s : σ) :
    r.post couple Q cv s = ∃ av, couple cv av s ∧ r.pred (Q av) s := by
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
    meet_prop_eq_and]

/-- The concretization of a state representation `st : Cσ → Aσ`: `pred P cs = P (st cs)`. -/
def ofStateRepr {Cσ Aσ : Type w} (st : Cσ → Aσ) : Concretization (Cσ → Prop) (Aσ → Prop) where
  pred P := fun cs => P (st cs)
  pred_mono h := fun cs => h (st cs)

@[simp] theorem ofStateRepr_pred {Cσ Aσ : Type w} (st : Cσ → Aσ) (P : Aσ → Prop) :
    (ofStateRepr st).pred P = fun cs => P (st cs) := rfl

/-- Composition: `(r₁.comp r₂).pred = r₁.pred ∘ r₂.pred`. -/
def comp {BPred : Type w} [Assertion BPred] (r₁ : Concretization CPred BPred)
    (r₂ : Concretization BPred APred) : Concretization CPred APred where
  pred := r₁.pred ∘ r₂.pred
  pred_mono h := r₁.pred_mono (r₂.pred_mono h)

/-- The identity concretization. -/
def id (Pred : Type w) [Assertion Pred] : Concretization Pred Pred where
  pred := _root_.id
  pred_mono h := h

end Concretization

/-! ## Purification

A program in `StateT σ Id` whose result and final state do not depend on the initial state
refines `pure (v, w) : Id (α × σ)`. The coupling `purifyCouple cv av s` holds when
`av = (cv, s)`: the final state becomes the second component of the abstract result. -/

section Purify

/-- The concretization from `Prop` to `σ → Prop`: `pred φ = fun _ => φ`. -/
noncomputable def purify (σ : Type) : Concretization (σ → Prop) Prop where
  pred φ := fun _ => φ
  pred_mono h := fun _ => h

/-- The coupling that reads the final state into the abstract result. -/
def purifyCouple {σ α : Type} : α → (α × σ) → (σ → Prop) :=
  fun cv av s => av = (cv, s)

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
