import Ascent.UB
import Ascent.WPCont

/-!
# `while` in `StateT σ UB`

`whileLoop cond body` is the least fixpoint of one unfolding of the loop, taken with
`partial_fixpoint` in the flat order of `UB`. A loop that runs forever denotes `none`, so its
`wp` is `⊥`. `whileLoop_unfold` states the fixpoint equation as a program:

```
whileLoop cond body =
  get >>= fun s => if cond s then body >>= fun _ => whileLoop cond body else pure ()
```

The flat order of `UB α` satisfies `WPCont`, so fixpoint induction applies to `partial_fixpoint`
definitions in `UB` and in `StateT σ UB`.
-/

open Std.WP Lean.Order Ascent

instance {α} : PartialOrder (UB α) := inferInstanceAs (PartialOrder (Option α))
instance {α} : CCPO (UB α) := inferInstanceAs (CCPO (Option α))
instance : MonoBind UB := inferInstanceAs (MonoBind Option)

instance {α} : WPCont (UB α) where
  wp_csup {ch} hch Q E := admissible_flatOrder (b := (none : Option α))
    (fun u => wp (show UB α from u) Q E → iSup fun x : {x // ch x} => wp x.1 Q E)
    (fun h => by change (⊥ : Prop) at h; rw [bot_prop_eq] at h; exact h.elim)
    ch hch fun x hx h => by
      rw [iSup_prop_eq_exists]
      exact ⟨⟨x, hx⟩, h⟩

/-- The fixpoint, at the state-passing type `σ → UB (Unit × σ)` that carries the `CCPO`. -/
def loopFix {σ : Type} (cond : σ → Bool) (body : StateT σ UB Unit) : StateT σ UB Unit :=
  fun s => if cond s then body s >>= fun p => loopFix cond body p.2 else pure ((), s)
partial_fixpoint

/-- `while cond do body`. The type is `StateT σ UB Unit`, so the `WP` instance of `StateT`
applies. -/
def whileLoop {σ : Type} (cond : σ → Bool) (body : StateT σ UB Unit) : StateT σ UB Unit :=
  loopFix cond body

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
