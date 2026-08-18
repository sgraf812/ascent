import AscentTests.TripleScaffold
import Ascent.Corres.RTriple

/-!
# Type strengthening: `ExceptT Unit (StateT σ Id) ↝ StateT σ Id`

A total computation typed in the failure monad is abstracted to one in the pure state monad.
The assertion lattice is unchanged (`pred = id`); the abstraction forbids failure by sending the
trivial abstract exception postcondition to `⊥` on the failure barrel. A refinement proof
therefore carries the obligation that the concrete program never fails. A throwing program
admits no refinement.
-/

open Std.WP Lean.Order Ascent

/-- Concrete failure monad of the type-strengthening phase. -/
abbrev TS (σ : Type) := ExceptT Unit (StateT σ Id)

/-- The type-strengthening concretization: identity on state assertions, failure forbidden. -/
def typeStrengthen (σ : Type) :
    Concretization (σ → Prop) (σ → Prop) (EPost.Cons (Unit → σ → Prop) EPost.Nil) EPost.Nil where
  pred := id
  ePred := fun _ => epost⟨fun _ => (⊥ : σ → Prop)⟩
  pred_mono h := h
  ePred_mono _ := PartialOrder.rel_refl

/-- A total state computation abstracts its lift into the failure monad: the never-fails
obligation is discharged by the `⊥` failure barrel in `typeStrengthen`. -/
theorem refines_lift {σ α : Type} (P : σ → Prop) (x : StateT σ Id α) :
    ⦃P⦄ x ⊑[typeStrengthen σ] (MonadLift.monadLift x : TS σ α) ⦃(⌜· = ·⌝)⦄ := by
  refine ⟨rwp_intro fun Qa Ea => ?_⟩
  have hQ : (typeStrengthen σ).post (fun av cv => ⌜av = cv⌝) Qa = Qa := by
    funext cv; simp only [Concretization.post_eq, typeStrengthen, id_eq]
  rw [hQ]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  exact WPMonad.le_wp_monadLift_ExceptT_apply x Qa (epost⟨fun _ => (⊥ : σ → Prop)⟩)

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
example : ⦃(⊤ : Nat → Prop)⦄ absInc ⊑[typeStrengthen Nat] concInc ⦃(⌜· = ·⌝)⦄ := by
  unfold absInc concInc
  refine .bind_eq (refines_lift _ _) fun x => ?_
  refine .bind_eq (refines_lift _ _) fun _ => ?_
  exact .pure_eq _ _ rfl

/-- A program that can fail has no type strengthening: `throw` forces the forbidden failure
barrel, so it refines no total abstraction. -/
example : ¬ ⦃(⊤ : Nat → Prop)⦄ (pure 0 : StateT Nat Id Nat)
    ⊑[typeStrengthen Nat] (throw () : TS Nat Nat) ⦃(⌜· = ·⌝)⦄ := by
  intro hsim
  have H := rwp_transport hsim.le_rwp (fun _ _ => True) EPost.Nil.mk
  have hthrow : wp (throw () : TS Nat Nat)
      ((typeStrengthen Nat).post (fun av cv => ⌜av = cv⌝) (fun _ _ => True))
      ((typeStrengthen Nat).ePost .mk EPost.Nil.mk) = (⊥ : Nat → Prop) := by
    simp [typeStrengthen, Concretization.ePost_nil, ExceptT.wp_apply_eq,
      WPMonadExact.wp_pure_eq]
  have hpure : (typeStrengthen Nat).pred
      (wp (pure 0 : StateT Nat Id Nat) (fun _ _ => True) EPost.Nil.mk) = (fun _ => True) := by
    simp [typeStrengthen, WPMonadExact.wp_pure_eq]
  rw [hthrow, hpure] at H
  have hfalse := H 0
  simp at hfalse

/-! ## Option-monad strengthening: `OptionT (StateT σ Id) ↝ StateT σ Id`

The same phase for the canonical AutoCorres failure monad, where failure carries no payload, so
the forbidden barrel is a single `⊥` (rather than a function of the error value). -/

/-- Concrete option failure monad. -/
abbrev OptS (σ : Type) := OptionT (StateT σ Id)

/-- The option-strengthening concretization: identity on state assertions, failure (`none`) forbidden. -/
def optionStrengthen (σ : Type) :
    Concretization (σ → Prop) (σ → Prop) (EPost.Cons (σ → Prop) EPost.Nil) EPost.Nil where
  pred := id
  ePred := fun _ => epost⟨(⊥ : σ → Prop)⟩
  pred_mono h := h
  ePred_mono _ := PartialOrder.rel_refl

/-- A total state computation abstracts its lift into the option monad. -/
theorem refines_liftOption {σ α : Type} (P : σ → Prop) (x : StateT σ Id α) :
    ⦃P⦄ x ⊑[optionStrengthen σ] (MonadLift.monadLift x : OptS σ α) ⦃(⌜· = ·⌝)⦄ := by
  refine ⟨rwp_intro fun Qa Ea => ?_⟩
  have hQ : (optionStrengthen σ).post (fun av cv => ⌜av = cv⌝) Qa = Qa := by
    funext cv; simp only [Concretization.post_eq, optionStrengthen, id_eq]
  rw [hQ]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  exact WPMonad.le_wp_monadLift_OptionT_apply x

/-- The same total increment, now strengthened out of the option monad. -/
def concIncOpt : OptS Nat Nat := do
  let x ← MonadLift.monadLift (get : StateT Nat Id Nat)
  MonadLift.monadLift (set (x + 1) : StateT Nat Id PUnit)
  pure x

example : ⦃(⊤ : Nat → Prop)⦄ absInc ⊑[optionStrengthen Nat] concIncOpt ⦃(⌜· = ·⌝)⦄ := by
  unfold absInc concIncOpt
  refine .bind_eq (refines_liftOption _ _) fun x => ?_
  refine .bind_eq (refines_liftOption _ _) fun _ => ?_
  exact .pure_eq _ _ rfl
