import Ascent.Corres.Basic

/-!
# Type strengthening: `ExceptT Unit (StateT σ Id) ↝ StateT σ Id`

A total computation typed in the failure monad is abstracted to one in the pure state monad.
The assertion lattice is unchanged (`pred = id`); the abstraction forbids failure by sending the
trivial abstract exception postcondition to `⊥` on the failure barrel. A `Corres` proof
therefore carries the obligation that the concrete program never fails. A throwing program
admits no correspondence.
-/

open Std.Internal.Do Lean.Order Ascent

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
theorem corres_lift {σ α : Type} (x : StateT σ Id α) :
    Corres (typeStrengthen σ) (.eq ⊤ (id : α → α)) x (MonadLift.monadLift x : TS σ α) := by
  intro Q E
  have hQ : (typeStrengthen σ).post (coupleEq id) Q = Q := by
    funext cv; simp only [Concretization.post_coupleEq, typeStrengthen, id_eq]
  rw [hQ]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  exact WPMonad.le_wp_monadLift_ExceptT_apply x Q (epost⟨fun _ => (⊥ : σ → Prop)⟩)

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
example : Corres (typeStrengthen Nat) (.eq ⊤ (id : Nat → Nat)) absInc concInc := by
  unfold absInc concInc
  refine corres_bind_top id id (corres_lift _) (fun x => ?_)
  refine corres_bind_top id id (corres_lift _) (fun _ => ?_)
  exact corres_pure ⊤ id rfl

/-- A program that can fail has no type strengthening: `throw` forces the forbidden failure
barrel, so no total abstraction corresponds to it. -/
example : ¬ Corres (typeStrengthen Nat) (.eq ⊤ (id : Nat → Nat))
    (pure 0 : StateT Nat Id Nat) (throw () : TS Nat Nat) := by
  intro hcorres
  have H := hcorres (fun _ _ => True) EPost.Nil.mk
  have hthrow : wp (throw () : TS Nat Nat) ((typeStrengthen Nat).post (coupleEq id) (fun _ _ => True))
      ((typeStrengthen Nat).ePred EPost.Nil.mk) = (⊥ : Nat → Prop) := by
    simp [typeStrengthen, ExceptT.wp_apply_eq, WPMonadExact.wp_pure_eq]
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
theorem corres_liftOption {σ α : Type} (x : StateT σ Id α) :
    Corres (optionStrengthen σ) (.eq ⊤ (id : α → α)) x (MonadLift.monadLift x : OptS σ α) := by
  intro Q E
  have hQ : (optionStrengthen σ).post (coupleEq id) Q = Q := by
    funext cv; simp only [Concretization.post_coupleEq, optionStrengthen, id_eq]
  rw [hQ]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  exact WPMonad.le_wp_monadLift_OptionT_apply x

/-- The same total increment, now strengthened out of the option monad. -/
def concIncOpt : OptS Nat Nat := do
  let x ← MonadLift.monadLift (get : StateT Nat Id Nat)
  MonadLift.monadLift (set (x + 1) : StateT Nat Id PUnit)
  pure x

example : Corres (optionStrengthen Nat) (.eq ⊤ (id : Nat → Nat)) absInc concIncOpt := by
  unfold absInc concIncOpt
  refine corres_bind_top id id (corres_liftOption _) (fun x => ?_)
  refine corres_bind_top id id (corres_liftOption _) (fun _ => ?_)
  exact corres_pure ⊤ id rfl
