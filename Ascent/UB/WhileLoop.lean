import Ascent.UB

/-!
# `while` in `StateT σ UB`

`whileLoop cond body` is the least fixpoint of one unfolding of the loop, taken with
`partial_fixpoint` in the flat order of `UB`. A loop that runs forever denotes `none`, so its
`wp` is `⊥`. `whileLoop_unfold` states the fixpoint equation as a program:

```
whileLoop cond body =
  get >>= fun s => if cond s then body >>= fun _ => whileLoop cond body else pure ()
```

`wp_csup_StateT` states that `wp` of the supremum of a chain of programs is below the supremum of
their `wp`s. Fixpoint induction over `loopFix` needs this fact.
-/

open Std.WP Lean.Order Ascent

instance {α} : PartialOrder (UB α) := inferInstanceAs (PartialOrder (Option α))
instance {α} : CCPO (UB α) := inferInstanceAs (CCPO (Option α))
instance : MonoBind UB := inferInstanceAs (MonoBind Option)

/-- The fixpoint, at the state-passing type `σ → UB (Unit × σ)` that carries the `CCPO`. -/
def loopFix {σ : Type} (cond : σ → Bool) (body : StateT σ UB Unit) : StateT σ UB Unit :=
  fun s => if cond s then body s >>= fun p => loopFix cond body p.2 else pure ((), s)
partial_fixpoint

/-- `while cond do body`. The type is `StateT σ UB Unit`, so the `WP` instance of `StateT`
applies. -/
def whileLoop {σ : Type} (cond : σ → Bool) (body : StateT σ UB Unit) : StateT σ UB Unit :=
  loopFix cond body

theorem wp_csup_StateT {σ α : Type} {c : (σ → UB (α × σ)) → Prop} (hc : chain c)
    (Q : α → σ → Prop) (E : EStack⟨⟩) :
    wp (show StateT σ UB α from CCPO.csup hc) Q E ⊑
      iSup fun f : {f // c f} => wp (show StateT σ UB α from f.1) Q E := by
  intro s
  have hadm := admissible_apply
    (β := fun _ => UB (α × σ))
    (fun s (u : UB (α × σ)) => wp u (fun p => Q p.1 p.2) E →
      (iSup fun f : {f // c f} => wp (show StateT σ UB α from f.1) Q E) s) s
    (admissible_flatOrder (b := (none : Option (α × σ))) _ (fun h => by
      change (⊥ : Prop) at h; rw [bot_prop_eq] at h; exact h.elim))
  simp only [StateT.wp_apply_eq, StateT.run] at hadm ⊢
  exact hadm c hc fun f hf h => by
    simp only [iSup_apply, iSup_prop_eq_exists]
    exact ⟨⟨f, hf⟩, by simpa [StateT.wp_apply_eq, StateT.run] using h⟩

theorem loopStep_eq {σ : Type} (cond : σ → Bool) (body k : StateT σ UB Unit) :
    (show StateT σ UB Unit from
      fun s => if cond s then body s >>= fun p => k p.2 else pure ((), s)) =
      (get >>= fun s => if cond s then body >>= fun _ => k else pure ()) := by
  funext s
  show _ = (if cond s then body >>= fun _ => k else pure ()) s
  split <;> rfl

theorem whileLoop_unfold {σ : Type} (cond : σ → Bool) (body : StateT σ UB Unit) :
    whileLoop cond body =
      (get >>= fun s => if cond s then body >>= fun _ => whileLoop cond body else pure ()) := by
  rw [← loopStep_eq]
  funext s
  rw [whileLoop, loopFix]

theorem wp_loopStep {σ : Type} (cond : σ → Bool) (body k : StateT σ UB Unit)
    (Q : Unit → σ → Prop) (E : EStack⟨⟩) (s : σ) :
    wp (get >>= fun s => if cond s then body >>= fun _ => k else pure ()) Q E s
      = if cond s then wp body (fun _ s' => wp k Q E s') E s else Q () s := by
  rw [← loopStep_eq, StateT.wp_apply_eq, StateT.run]
  split <;> simp only [UB.wp_bind_eq, UB.wp_pure_eq, StateT.wp_apply_eq, StateT.run]

theorem wp_whileLoop {σ : Type} (cond : σ → Bool) (body : StateT σ UB Unit)
    (Q : Unit → σ → Prop) (E : EStack⟨⟩) (s : σ) :
    wp (whileLoop cond body) Q E s
      = if cond s then wp body (fun _ s' => wp (whileLoop cond body) Q E s') E s else Q () s := by
  conv => lhs; rw [whileLoop_unfold]
  exact wp_loopStep cond body _ Q E s
