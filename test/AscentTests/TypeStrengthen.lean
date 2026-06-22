import Ascent.Corres.Basic

/-!
# Type strengthening: `ExceptT Unit (StateT σ Id) ↝ StateT σ Id`

A total computation typed in the failure monad is abstracted to one in the pure state monad.
The assertion lattice is unchanged (`γP = id`); the abstraction forbids failure by sending the
trivial abstract exception postcondition to `⊥` on the failure barrel. A `Corres` proof
therefore carries the obligation that the concrete program never fails. A throwing program
admits no correspondence.
-/

open Std.Internal.Do Lean.Order Ascent

/-- Concrete failure monad of the type-strengthening phase. -/
abbrev TS (σ : Type) := ExceptT Unit (StateT σ Id)

/-- The type-strengthening refinement: identity on state assertions, failure forbidden. -/
def typeStrengthen (σ : Type) :
    Refinement (σ → Prop) (σ → Prop) (EPost.Cons (Unit → σ → Prop) EPost.Nil) EPost.Nil where
  γP := id
  γE := fun _ => epost⟨fun _ => (⊥ : σ → Prop)⟩
  γP_mono h := h
  γE_mono _ := PartialOrder.rel_refl

/-- `StateT Nat Id` interprets `pure` exactly (one direction; the other is `pure_le_wp_pure`). -/
theorem stPureLe {α} (a : α) (post : α → Nat → Prop) (epost : EPost.Nil) :
    wp (pure a : StateT Nat Id α) post epost ⊑ post a := by intro s; exact PartialOrder.rel_refl

/-- `StateT Nat Id` interprets `bind` exactly (one direction). -/
theorem stBindLe {α β} (x : StateT Nat Id α) (f : α → StateT Nat Id β)
    (post : β → Nat → Prop) (epost : EPost.Nil) :
    wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost := by
  intro s; exact PartialOrder.rel_refl

instance : LawfulRefinement (typeStrengthen Nat) (TS Nat) (StateT Nat Id) :=
  .ofWPMorphism stPureLe stBindLe

/-- A total state computation abstracts its lift into the failure monad: the never-fails
obligation is discharged by the `⊥` failure barrel in `typeStrengthen`. -/
theorem corres_lift {σ α : Type} (x : StateT σ Id α) :
    Corres (typeStrengthen σ) (id : α → α) x (MonadLift.monadLift x : TS σ α) := by
  intro Q E
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
example : Corres (typeStrengthen Nat) (id : Nat → Nat) absInc concInc := by
  unfold absInc concInc
  refine corres_bind id id (corres_lift _) (fun x => ?_)
  refine corres_bind id id (corres_lift _) (fun _ => ?_)
  exact corres_pure id rfl

/-- A program that can fail has no type strengthening: `throw` forces the forbidden failure
barrel, so no total abstraction corresponds to it. -/
example : ¬ Corres (typeStrengthen Nat) (id : Nat → Nat)
    (pure 0 : StateT Nat Id Nat) (throw () : TS Nat Nat) := by
  intro hcorres
  have H := hcorres (fun _ _ => True) EPost.Nil.mk
  have hthrow : wp (throw () : TS Nat Nat) ((typeStrengthen Nat).γQ id (fun _ _ => True))
      ((typeStrengthen Nat).γE EPost.Nil.mk) = (⊥ : Nat → Prop) := by
    simp [typeStrengthen, ExceptT.wp_apply_eq, wp_pure_eq stPureLe]
  have hpure : (typeStrengthen Nat).γP
      (wp (pure 0 : StateT Nat Id Nat) (fun _ _ => True) EPost.Nil.mk) = (fun _ => True) := by
    simp [typeStrengthen, wp_pure_eq stPureLe]
  rw [hthrow, hpure] at H
  have hfalse := H 0 trivial
  simp at hfalse
