import Ascent.Corres.Sim

/-!
# The `UB` (undefined-behavior) effect

`UB` is `Option` with a weakest precondition reading failure as undefined behavior: `wp fail = ⊥`,
so a failed guard makes every postcondition unprovable. This is the monad in which AutoCorres'
emitted `guard` statements live. A value-dependent side-condition (e.g. no-overflow) rides along
inside the abstract program and is threaded by `wp` through `bind`, rather than being a precondition
on the relation.
-/

open Std.Internal.Do Lean.Order Ascent

/-- `Option` reinterpreted so failure is undefined behavior: failure is `⊥`, not a handled exception. -/
def UB (α : Type) := Option α

namespace UB

instance : Monad UB := inferInstanceAs (Monad Option)
instance : LawfulMonad UB := inferInstanceAs (LawfulMonad Option)

/-- Undefined behavior. -/
def fail : UB α := none

/-- Return `a`, but fail (undefined behavior) unless the guard `g` holds. -/
def guardRet (g : Prop) [Decidable g] (a : α) : UB α := if g then pure a else fail

@[instance_reducible] def wpInst {α} : WP (UB α) α Prop EPost.Nil where
  wpTrans x := ⟨fun post _ => match x with | none => ⊥ | some a => post a⟩
  wp_trans_monotone x := by
    intro post post' epost epost' _ hpost
    cases x with
    | none => exact PartialOrder.rel_refl
    | some a => exact hpost a

instance instWPMonad : WPMonad UB Prop EPost.Nil where
  toWP _ := wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f := by intro post epost; cases x <;> exact PartialOrder.rel_refl

@[simp] theorem wp_pure_eq {α} (a : α) (Q : α → Prop) (E : EPost.Nil) :
    wp (pure a : UB α) Q E = Q a := rfl

@[simp] theorem wp_fail_eq {α} (Q : α → Prop) (E : EPost.Nil) :
    wp (UB.fail : UB α) Q E = ⊥ := rfl

@[simp] theorem wp_map_eq {α β} (f : α → β) (x : UB α) (Q : β → Prop) (E : EPost.Nil) :
    wp (f <$> x) Q E = wp x (fun a => Q (f a)) E := by cases x <;> rfl

@[spec] theorem UB.fail_spec :
    ⦃⊥⦄ UB.fail ⦃Q; E⦄ := ⟨bot_le _⟩

theorem wp_pure_le {α} (a : α) (post : α → Prop) (epost : EPost.Nil) :
    wp (pure a : UB α) post epost ⊑ post a := PartialOrder.rel_refl

theorem wp_bind_le {α β} (x : UB α) (f : α → UB β) (post : β → Prop) (epost : EPost.Nil) :
    wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost := by
  cases x <;> exact PartialOrder.rel_refl

/-- `UB`'s `wp` interprets `bind` exactly. -/
theorem wp_bind_eq {α β} (x : UB α) (f : α → UB β) (post : β → Prop) (epost : EPost.Nil) :
    wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost := by
  cases x <;> rfl

/-- `UB`'s `wp` conjoins postconditions (the monad is deterministic). -/
theorem wp_and {α} (x : UB α) (P R : α → Prop) (epost : EPost.Nil)
    (hP : wp x P epost) (hR : wp x R epost) : wp x (fun a => P a ∧ R a) epost := by
  cases x with
  | none => exact hP
  | some a => exact ⟨hP, hR⟩

/-- `UB`'s `wp` is conjunctive (the lattice form of `wp_and`). -/
theorem wp_meet {α} (x : UB α) (A B : α → Prop) (E : EPost.Nil) :
    wp x A E ⊓ wp x B E ⊑ wp x (fun v => A v ⊓ B v) E := by
  cases x with
  | none => exact meet_le_left _ _
  | some a => exact PartialOrder.rel_refl

end UB

/-- `⊤` is the identity of `⊓` (the `⊤` precondition adds nothing). -/
@[simp] theorem top_meet {α} [Assertion α] (x : α) : (⊤ : α) ⊓ x = x :=
  PartialOrder.rel_antisymm (meet_le_right _ _) (le_meet _ _ _ (le_top _) PartialOrder.rel_refl)

/-- `wp` distributes over `if`. Stated generally; `simp` cannot derive this from `apply_ite`
because the `ite` is a nested argument of `wp` rather than its sole argument. -/
@[simp] theorem wp_ite {Prog Value Pred EPred} [Assertion Pred] [Assertion EPred]
    [WP Prog Value Pred EPred] (c : Prop) [Decidable c]
    (a b : Prog) (post : Value → Pred) (epost : EPred) :
    wp (if c then a else b) post epost = if c then wp a post epost else wp b post epost := by
  split <;> rfl

/-- `UB`'s `wp` is exact: it pins `pure`/`bind` from both sides. -/
instance : WPMonadExact UB Prop EPost.Nil where
  wp_pure_le := UB.wp_pure_le
  wp_bind_le := UB.wp_bind_le

/-- `UB`'s `wp` is conjunctive. -/
instance {α} : WPConjunctive (UB α) α Prop EPost.Nil where
  wp_meet_wp_le x Q₁ Q₂ E := by
    rw [show (Q₁ ⊓ Q₂) = fun v => Q₁ v ⊓ Q₂ v from funext fun v => meet_apply Q₁ Q₂ v]
    exact UB.wp_meet x Q₁ Q₂ E

/-- A guarded pure value abstracts a pure value: under the guard, the precondition entails the
coupling; on a failed guard the abstract program fails and the simulation is discharged
trivially. The no-overflow obligation lives in the guard `g`, threaded by `wp`, not in the
precondition. -/
theorem Ascent.SimTriple.guardRet {AV CV : Type} {g : Prop} [Decidable g] {P : Prop}
    {Q : AV → CV → Prop} (a : AV) (c : CV) (h : g → P ⊑ Q a c) :
    ⦃P⦄ (UB.guardRet g a) ⊑[Concretization.id Prop EPost.Nil] (Pure.pure c : Id CV) ⦃Q; ()⦄ := by
  refine SimTriple.intro fun Qa Ea => ?_
  by_cases hg : g
  · rw [show UB.guardRet g a = Pure.pure a from by simp [UB.guardRet, hg]]
    show P ⊓ Qa a ⊑ (Concretization.id Prop EPost.Nil).post Q Qa c
    refine CompleteLattice.le_iSup_of_le a ?_
    exact le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) (h hg)) (meet_le_right _ _)
  · rw [show UB.guardRet g a = UB.fail from by simp [UB.guardRet, hg]]
    show P ⊓ (⊥ : Prop) ⊑ _
    exact PartialOrder.rel_trans (meet_le_right _ _) (bot_le _)

/-- A guarded pure value abstracts a pure value, when the guard implies the value relation. The
no-overflow obligation lives in the guard `g`, threaded by `wp`, not in a precondition. -/
theorem corres_guardRet {CVal AVal} {g : Prop} [Decidable g] (pre : Prop) (couple : CVal → AVal)
    {a : AVal} {c : CVal} (h : g → couple c = a) :
    Corres (Concretization.id Prop EPost.Nil) (.eq pre couple) (UB.guardRet g a) (pure c : Id CVal) := by
  intro Q E
  have hQ : (Concretization.id Prop EPost.Nil).post (coupleEq couple) Q = fun cv => Q (couple cv) := by
    funext cv; simp only [Concretization.post_coupleEq, Concretization.id, id_eq]
  rw [hQ]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  by_cases hg : g
  · have hh : couple c = a := h hg
    subst hh
    rw [show UB.guardRet g (couple c) = pure (couple c) from by simp [UB.guardRet, hg]]
    exact PartialOrder.rel_refl
  · rw [show UB.guardRet g a = UB.fail from by simp [UB.guardRet, hg]]
    show (⊥ : Prop) ⊑ Q (couple c)
    exact bot_le _
