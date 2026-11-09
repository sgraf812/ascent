import Ascent.UB

/-!
# Pure refinement

`PureRefinement cv av P Q` is the refinement triple of a pure concrete value `cv` and a pure
abstract value `av`: under the precondition `P`, the values are related by `Q`. The
`@[ascend_pure]` rules derive it by recursion over `cv`, and each bind of a concrete value `c` to
an abstract value `x` contributes the hypothesis `PureRefinement c x True Q`.

`Refinement.pure_rel` lifts `PureRefinement` to programs: the abstract program of `pure cv` is
`do UB.assume P; pure av`, and the continuation receives `cv` as a variable `c` together with the
hypothesis `PureRefinement c x True Q`.
-/

open Std.WP Lean.Order

namespace Ascent

/-- The relation `f a = b` of the function `f`. -/
def FunRel (f : α → β) : α → β → Prop := fun a b => f a = b

@[simp] theorem funRel_iff {f : α → β} {a : α} {b : β} : FunRel f a b ↔ f a = b := Iff.rfl

/-- Under the precondition `P`, the concrete value `cv` and the abstract value `av` are related
by `Q`. -/
def PureRefinement {CV : Type u} {AV : Type v} (cv : CV) (av : AV) (P : Prop) (Q : CV → AV → Prop) :
    Prop :=
  P → Q cv av

section PureRefinement
variable {CV : Type u} {AV : Type v} {cv : CV} {av : AV} {P P' : Prop} {Q : CV → AV → Prop}

theorem pureRefinement_iff : PureRefinement cv av P Q ↔ (P → Q cv av) := Iff.rfl

theorem PureRefinement.rel (h : PureRefinement cv av True Q) : Q cv av := h trivial

theorem PureRefinement.of_rel (h : Q cv av) : PureRefinement cv av True Q := fun _ => h

@[grind norm] theorem PureRefinement.true_eq : PureRefinement cv av True Q = Q cv av :=
  propext ⟨PureRefinement.rel, PureRefinement.of_rel⟩

theorem PureRefinement.of_pre_eq (h : PureRefinement cv av P Q) (e : P = P') :
    PureRefinement cv av P' Q :=
  e ▸ h

theorem PureRefinement.weaken_pre (h : PureRefinement cv av P Q) (hpre : P' → P) :
    PureRefinement cv av P' Q :=
  fun h' => h (hpre h')

theorem PureRefinement.of_val_eq {av' : AV} (h : PureRefinement cv av P Q) (e : av = av') :
    PureRefinement cv av' P Q :=
  e ▸ h

theorem PureRefinement.of_cv_eq {cv' : CV} (h : PureRefinement cv' av P Q) (e : cv = cv') :
    PureRefinement cv av P Q :=
  e ▸ h

theorem PureRefinement.funRel {f : CV → AV} : PureRefinement cv (f cv) True (FunRel f) :=
  PureRefinement.of_rel rfl

end PureRefinement

theorem Refinement.fail {CM : Type → Type} [Monad CM] [WPMonad CM Prop EStack⟨⟩] {CV AV : Type}
    {P : Prop} {Q : CV → AV → Prop} {E : EStack⟨⟩} (c : CM CV) :
    ⦃P⦄ c ⪯[Concretization.id Prop] (UB.fail : UB AV) ⦃Q; E⦄ :=
  ⟨wrp_intro fun _ _ => PartialOrder.rel_trans (meet_le_right _ _) (bot_le _)⟩

theorem Refinement.pure_rel {CM : Type → Type} [Monad CM] [WPMonad CM Prop EStack⟨⟩]
    {CV AV : Type} {cv : CV} {av : AV} {P : Prop} {R : CV → AV → Prop}
    (h : PureRefinement cv av P R) {Q : CV → AV → Prop} {E : EStack⟨⟩} :
    ⦃(∀ c x, c = cv → PureRefinement c x True R → Q c x)⦄ (Pure.pure cv : CM CV)
      ⪯[Concretization.id Prop] (UB.assume P >>= fun _ => Pure.pure av) ⦃Q; E⦄ := by
  by_cases hP : P
  · rw [UB.assume_bind_of_pos hP]
    exact (Refinement.pure cv av).weaken fun hpre =>
      hpre cv av rfl (PureRefinement.of_rel (h hP))
  · rw [UB.assume_bind_of_neg hP]
    exact Refinement.fail _

end Ascent
