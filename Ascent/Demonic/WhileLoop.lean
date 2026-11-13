import Ascent.Demonic
import Ascent.WPCont

/-!
# `while` in `StateT σ Demonic`

`whileLoop cond body` is the least fixpoint of one unfolding of the loop, taken with
`partial_fixpoint` in the flat order of `Demonic`. A loop that runs forever denotes `abort`, so its
`wp` is `⊥`. `whileLoop_unfold` states the fixpoint equation as a program:

```
whileLoop cond body =
  get >>= fun s => if cond s then body >>= fun _ => whileLoop cond body else pure ()
```

The flat order of `Demonic α` satisfies `WPCont`, so fixpoint induction applies to `partial_fixpoint`
definitions in `Demonic` and in `StateT σ Demonic`.
-/

open Std.WP Lean.Order Ascent

instance {α : Type} : PartialOrder (Demonic α) :=
  inferInstanceAs (PartialOrder (FlatOrder (Demonic.abort : Demonic α)))
instance {α : Type} : CCPO (Demonic α) := inferInstanceAs (CCPO (FlatOrder (Demonic.abort : Demonic α)))

theorem Demonic.eq_of_le {α : Type} {x y : Demonic α} (h : x ⊑ y) (hx : x ≠ Demonic.abort) : x = y := by
  cases h with
  | bot => exact absurd rfl hx
  | refl => rfl

theorem Demonic.bind_congr {α β : Type} {x : Demonic α} {f₁ f₂ : α → Demonic β}
    (h : ∀ a, x.outs a → f₁ a = f₂ a) : (x >>= f₁) = (x >>= f₂) := by
  by_cases ht : x.wpD fun _ => True
  · refine Demonic.ext (funext fun Q => ?_)
    show (x.wpD fun a => (f₁ a).wpD Q) = x.wpD fun a => (f₂ a).wpD Q
    rw [propext (Demonic.wpD_iff ht _), propext (Demonic.wpD_iff ht _)]
    exact propext (forall_congr' fun a => imp_congr_right fun ha => by rw [h a ha])
  · rw [Demonic.eq_abort ht]
    rfl

theorem Demonic.bind_of_abort {α β : Type} {x : Demonic α} {f : α → Demonic β} {a : α}
    (ha : x.outs a) (hf : f a = Demonic.abort) : (x >>= f) = Demonic.abort := by
  by_cases ht : x.wpD fun _ => True
  · refine Demonic.ext (funext fun Q => propext ⟨fun hw => ?_, False.elim⟩)
    have := (Demonic.wpD_iff ht _).mp hw a ha
    rw [hf] at this
    exact this
  · rw [Demonic.eq_abort ht]
    rfl

instance : MonoBind Demonic where
  bind_mono_left h := by
    cases h
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right {_ _ a f₁ f₂} h := by
    open Classical in
    by_cases hab : ∃ x, a.outs x ∧ f₁ x = Demonic.abort
    · obtain ⟨x, hx, hf⟩ := hab
      rw [Demonic.bind_of_abort hx hf]
      exact FlatOrder.rel.bot
    · rw [Demonic.bind_congr fun x hs => Demonic.eq_of_le (h x) fun ha => hab ⟨x, hs, ha⟩]

instance {α : Type} : WPCont (Demonic α) where
  wp_csup {ch} hch Q E := admissible_flatOrder (b := (Demonic.abort : Demonic α))
    (fun u => wp (show Demonic α from u) Q E → iSup fun x : {x // ch x} => wp x.1 Q E)
    (fun h => h.elim)
    ch hch fun x hx h => by
      rw [iSup_prop_eq_exists]
      exact ⟨⟨x, hx⟩, h⟩

/-- The fixpoint, at the state-passing type `σ → Demonic (Unit × σ)` that carries the `CCPO`. -/
def loopFix {σ : Type} (cond : σ → Bool) (body : StateT σ Demonic Unit) : StateT σ Demonic Unit :=
  fun s => if cond s then body s >>= fun p => loopFix cond body p.2 else pure ((), s)
partial_fixpoint

/-- `while cond do body`. The type is `StateT σ Demonic Unit`, so the `WP` instance of `StateT`
applies. -/
def whileLoop {σ : Type} (cond : σ → Bool) (body : StateT σ Demonic Unit) : StateT σ Demonic Unit :=
  loopFix cond body

theorem loopStep_eq {σ : Type} (cond : σ → Bool) (body k : StateT σ Demonic Unit) :
    (show StateT σ Demonic Unit from
      fun s => if cond s then body s >>= fun p => k p.2 else pure ((), s)) =
      (get >>= fun s => if cond s then body >>= fun _ => k else pure ()) := by
  funext s
  show _ = (if cond s then body >>= fun _ => k else pure ()) s
  split <;> rfl

theorem whileLoop_unfold {σ : Type} (cond : σ → Bool) (body : StateT σ Demonic Unit) :
    whileLoop cond body =
      (get >>= fun s => if cond s then body >>= fun _ => whileLoop cond body else pure ()) := by
  rw [← loopStep_eq]
  funext s
  rw [whileLoop, loopFix]

theorem wp_loopStep {σ : Type} (cond : σ → Bool) (body k : StateT σ Demonic Unit)
    (Q : Unit → σ → Prop) (E : EStack⟨⟩) (s : σ) :
    wp (get >>= fun s => if cond s then body >>= fun _ => k else pure ()) Q E s
      = if cond s then wp body (fun _ s' => wp k Q E s') E s else Q () s := by
  rw [← loopStep_eq, StateT.wp_apply_eq, StateT.run]
  split <;> simp only [Demonic.wp_bind_eq, Demonic.wp_pure_eq, StateT.wp_apply_eq, StateT.run]

theorem wp_whileLoop {σ : Type} (cond : σ → Bool) (body : StateT σ Demonic Unit)
    (Q : Unit → σ → Prop) (E : EStack⟨⟩) (s : σ) :
    wp (whileLoop cond body) Q E s
      = if cond s then wp body (fun _ s' => wp (whileLoop cond body) Q E s') E s else Q () s := by
  conv => lhs; rw [whileLoop_unfold]
  exact wp_loopStep cond body _ Q E s
