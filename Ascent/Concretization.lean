import Std.WP
import Ascent.WPMonadExact

/-!
# Concretization

A `Concretization CPred APred` is a monotone map `pred : APred → CPred` from abstract assertions
to concrete assertions.

Example. `ofStateRepr st` for `st : Cσ → Aσ` has `pred P cs = P (st cs)`. Under it the abstract
assertion `fun as => as.1 < 10` becomes `fun cs => (st cs).1 < 10`.

`post` extends `pred` to postconditions on values. For a return relation `Q : CVal → AVal → CPred`
and an abstract postcondition `Qa : AVal → APred`, `post Q Qa cv = ⨆ av, Q cv av ⊓ pred (Qa av)`:
some abstract value is related to `cv` and satisfies `Qa`. For a functional return relation
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

/-- The concrete postcondition for the return relation `Q` and the abstract postcondition `Qa`:
`post Q Qa cv = ⨆ av, Q cv av ⊓ pred (Qa av)`. -/
noncomputable def post (r : Concretization CPred APred) {CVal AVal : Type _}
    (Q : CVal → AVal → CPred) (Qa : AVal → APred) : CVal → CPred :=
  fun cv => iSup fun av => Q cv av ⊓ r.pred (Qa av)

@[simp] theorem post_eq (r : Concretization CPred APred) {CVal AVal : Type _}
    (f : CVal → AVal) (Qa : AVal → APred) :
    r.post (fun cv av => (⌜f cv = av⌝ : CPred)) Qa = fun cv => r.pred (Qa (f cv)) := by
  funext cv
  refine PartialOrder.rel_antisymm (iSup_le _ _ fun av => ?_) ?_
  · exact CompleteLattice.ofProp_meet_le (by rintro rfl; exact PartialOrder.rel_refl)
  · refine PartialOrder.rel_trans ?_
      (le_iSup (fun av => (⌜f cv = av⌝ : CPred) ⊓ r.pred (Qa av)) (f cv))
    exact le_meet _ _ _ (CompleteLattice.le_ofProp _ _ rfl) PartialOrder.rel_refl

theorem post_prop {APred : Type} [Assertion APred]
    (r : Concretization Prop APred) {CVal AVal : Type _}
    (Q : CVal → AVal → Prop) (Qa : AVal → APred) (cv : CVal) :
    r.post Q Qa cv = ∃ av, Q cv av ∧ r.pred (Qa av) := by
  simp only [Concretization.post, iSup_prop_eq_exists, meet_prop_eq_and]

theorem post_pi {σ : Type} {APred : Type} [Assertion APred]
    (r : Concretization (σ → Prop) APred) {CVal AVal : Type _}
    (Q : CVal → AVal → σ → Prop) (Qa : AVal → APred) (cv : CVal) (s : σ) :
    r.post Q Qa cv s = ∃ av, Q cv av s ∧ r.pred (Qa av) s := by
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
    meet_prop_eq_and]

/-- The concretization of a state representation `st : Cσ → Aσ`: `pred P cs = P (st cs)`. -/
def ofStateRepr {Cσ Aσ : Type w} (st : Cσ → Aσ) : Concretization (Cσ → Prop) (Aσ → Prop) where
  pred P := fun cs => P (st cs)
  pred_mono h := fun cs => h (st cs)

@[simp] theorem ofStateRepr_pred {Cσ Aσ : Type w} (st : Cσ → Aσ) (P : Aσ → Prop) :
    (ofStateRepr st).pred P = fun cs => P (st cs) := rfl

/-- The concretization of a state relation `J : Cσ → Aσ → Prop`:
`pred P cs = ∃ as, J cs as ∧ P as`. -/
def ofStateRel {Cσ Aσ : Type w} (J : Cσ → Aσ → Prop) : Concretization (Cσ → Prop) (Aσ → Prop) where
  pred P := fun cs => ∃ as, J cs as ∧ P as
  pred_mono h := fun _ ⟨as, hJ, hP⟩ => ⟨as, hJ, h as hP⟩

@[simp] theorem ofStateRel_pred {Cσ Aσ : Type w} (J : Cσ → Aσ → Prop) (P : Aσ → Prop) :
    (ofStateRel J).pred P = fun cs => ∃ as, J cs as ∧ P as := rfl

theorem ofStateRel_pred_iSup {Cσ Aσ : Type w} (J : Cσ → Aσ → Prop) {ι : Type _}
    (X : ι → Aσ → Prop) :
    (ofStateRel J).pred (iSup X) ⊑ iSup fun i => (ofStateRel J).pred (X i) := by
  rintro cs ⟨as, hJ, hX⟩
  simp only [iSup_apply, iSup_prop_eq_exists] at hX ⊢
  obtain ⟨i, hi⟩ := hX
  exact ⟨i, as, hJ, hi⟩

@[simp] theorem ofStateRel_post_top {Cσ Aσ : Type w} {CVal AVal : Type _} (J : Cσ → Aσ → Prop)
    (Qa : AVal → Aσ → Prop) :
    (ofStateRel J).post (fun (_ : CVal) (_ : AVal) => ⊤) Qa
      = fun (_ : CVal) cs => ∃ av as, J cs as ∧ Qa av as := by
  funext cv cs
  simp only [Concretization.post, ofStateRel_pred, iSup_apply, meet_apply, top_apply,
    iSup_prop_eq_exists, meet_prop_eq_and, top_prop_eq, true_and]

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
refines `pure (v, w) : Id (α × σ)`. The return relation `purifyRel cv av s` holds when
`av = (cv, s)`: the final state becomes the second component of the abstract result. -/

section Purify

/-- The concretization from `Prop` to `σ → Prop`: `pred φ = fun _ => φ`. -/
noncomputable def purify (σ : Type) : Concretization (σ → Prop) Prop where
  pred φ := fun _ => φ
  pred_mono h := fun _ => h

/-- The return relation that reads the final state into the abstract result. -/
def purifyRel {σ α : Type} : α → (α × σ) → (σ → Prop) :=
  fun cv av s => av = (cv, s)

@[simp] theorem purify_post {σ α : Type} (Q : (α × σ) → Prop) :
    (purify σ).post purifyRel Q = fun cv s => Q (cv, s) := by
  funext cv s
  simp only [Concretization.post, purify, purifyRel, iSup_apply, meet_apply, iSup_prop_eq_exists,
    meet_prop_eq_and]
  apply propext
  constructor
  · rintro ⟨i, rfl, h⟩; exact h
  · intro h; exact ⟨(cv, s), rfl, h⟩

end Purify

end Ascent
