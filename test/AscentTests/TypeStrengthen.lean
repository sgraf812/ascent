import AscentTests.TripleScaffold
import Ascent.Refinement

/-!
# Type strengthening: `ExceptT Unit (StateT σ Id) ↝ StateT σ Id`

A total computation in the failure monad refines the same computation in the state monad. The
concretization is `Concretization.id`. The concrete exception layer has no abstract counterpart,
so the exception relation is a postcondition on the concrete failure, and the default `⊥` forbids
it. A program that throws refines no program in the state monad.
-/

open Std.WP Lean.Order Ascent

/-- Concrete failure monad of the type-strengthening phase. -/
abbrev TS (σ : Type) := ExceptT Unit (StateT σ Id)

/-- A total state computation abstracts its lift into the failure monad: the never-fails
obligation is the default exception relation `⊥`. -/
theorem refines_lift {σ α : Type} (P : σ → Prop) (x : StateT σ Id α) :
    ⦃P⦄ (MonadLift.monadLift x : TS σ α) ⪯[Concretization.id (σ → Prop)] x ⦃(⌜· = ·⌝)⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  have hQ : (Concretization.id (σ → Prop)).post (fun cv av => ⌜cv = av⌝) Qa = Qa := by
    funext cv; simp only [Concretization.post_eq, Concretization.id, id_eq]
  rw [hQ]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  exact WPMonad.le_wp_monadLift_ExceptT_apply (ε := Unit) x Qa _

/-- Abstract (total) increment in the state monad. -/
def absInc : StateT Nat Id Nat := do
  let x ← get
  set (x + 1)
  pure x

/-- Concrete increment in the failure monad, built from lifts of the total state operations. -/
def concInc : TS Nat Nat := do
  let x ← MonadLift.monadLift (get : StateT Nat Id Nat)
  MonadLift.monadLift (set (x + 1) : StateT Nat Id PUnit)
  pure x

/-- The total failure-monad program abstracts to the pure state program. -/
example : ⦃(⊤ : Nat → Prop)⦄ concInc ⪯[Concretization.id (Nat → Prop)] absInc ⦃(⌜· = ·⌝)⦄ := by
  unfold absInc concInc
  refine .bind_eq (refines_lift _ _) fun x => ?_
  refine .bind_eq (refines_lift _ _) fun _ => ?_
  exact .pure_eq _ _ rfl

/-- A program that throws refines no program in the state monad. -/
example : ¬ ⦃(⊤ : Nat → Prop)⦄ (throw () : TS Nat Nat)
    ⪯[Concretization.id (Nat → Prop)] (pure 0 : StateT Nat Id Nat) ⦃(⌜· = ·⌝)⦄ := by
  intro hsim
  have H := wrp_transport hsim.le_wrp (fun _ _ => True) estack⟨⟩
  have hthrow : wp (throw () : TS Nat Nat)
      ((Concretization.id (Nat → Prop)).post (fun cv av => ⌜cv = av⌝) (fun _ _ => True))
      (EPostsConcretization.ePosts (CEPosts := EStack⟨Unit → Nat → Prop⟩)
        (Concretization.id (Nat → Prop)) ⊥ estack⟨⟩) = (⊥ : Nat → Prop) := by
    simp [Concretization.id, EPostsConcretization.ePosts_cons_fill, ExceptT.wp_apply_eq,
      WPMonadExact.wp_pure_eq]
  have hpure : (Concretization.id (Nat → Prop)).pred
      (wp (pure 0 : StateT Nat Id Nat) (fun _ _ => True) estack⟨⟩) = (fun _ => True) := by
    simp [Concretization.id, WPMonadExact.wp_pure_eq]
  rw [hthrow, hpure] at H
  have hfalse := H 0
  simp at hfalse

/-! ## Option-monad strengthening: `OptionT (StateT σ Id) ↝ StateT σ Id`

The same phase for `OptionT`, the failure monad of AutoCorres. -/

/-- Concrete option failure monad. -/
abbrev OptS (σ : Type) := OptionT (StateT σ Id)

/-- A total state computation abstracts its lift into the option monad. -/
theorem refines_liftOption {σ α : Type} (P : σ → Prop) (x : StateT σ Id α) :
    ⦃P⦄ (MonadLift.monadLift x : OptS σ α) ⪯[Concretization.id (σ → Prop)] x ⦃(⌜· = ·⌝)⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  have hQ : (Concretization.id (σ → Prop)).post (fun cv av => ⌜cv = av⌝) Qa = Qa := by
    funext cv; simp only [Concretization.post_eq, Concretization.id, id_eq]
  rw [hQ]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  exact WPMonad.le_wp_monadLift_OptionT_apply x

/-- The same total increment, now strengthened out of the option monad. -/
def concIncOpt : OptS Nat Nat := do
  let x ← MonadLift.monadLift (get : StateT Nat Id Nat)
  MonadLift.monadLift (set (x + 1) : StateT Nat Id PUnit)
  pure x

example : ⦃(⊤ : Nat → Prop)⦄ concIncOpt ⪯[Concretization.id (Nat → Prop)] absInc ⦃(⌜· = ·⌝)⦄ := by
  unfold absInc concIncOpt
  refine .bind_eq (refines_liftOption _ _) fun x => ?_
  refine .bind_eq (refines_liftOption _ _) fun _ => ?_
  exact .pure_eq _ _ rfl
