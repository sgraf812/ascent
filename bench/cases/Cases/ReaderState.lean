import Cases.Setup.State

/-!
# `ReaderState`: a reader over a state

The mirror of the `vcgen` case `ReaderState`, in `RM := ReaderT Nat (StateT Nat Demonic)`. Each
step reads the reader value `r`, adds it to the state and subtracts it again. The rules bind the
reader value and each read state to variables of the abstract program, and `wrp_bind` decomposes
the binds of `step; loop n` nested to the left. The family stresses goals with two state arguments and the value solver with two
kinds of entries.
-/

open Std.WP Lean.Order Distillery

namespace DistillBench.ReaderState

instance {ρ : Type u} {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m Pred EPosts] :
    WPMonadExact (ReaderT ρ m) (ρ → Pred) EPosts where
  wp_pure_le a := fun post epost r => by
    rw [ReaderT.wp_apply_eq]
    exact WPMonadExact.wp_pure_le (m := m) a (fun a => post a r) epost
  wp_bind_le x f := fun post epost r => by
    simp only [ReaderT.wp_apply_eq]
    exact WPMonadExact.wp_bind_le (m := m) (x.run r) (fun a => (f a).run r) (fun a => post a r) epost

abbrev RM := ReaderT Nat (StateT Nat Demonic)

abbrev γ : Concretization (Nat → Nat → Prop) (Nat → Nat → Prop) := Concretization.id _

section
variable {E : EStack⟨⟩}

theorem wp_read_RM (Q : Nat → Nat → Nat → Prop) (r s : Nat) : wp (read : RM Nat) Q E r s = Q r r s := rfl
theorem wp_get_RM (Q : Nat → Nat → Nat → Prop) (r s : Nat) : wp (get : RM Nat) Q E r s = Q s r s := rfl
theorem wp_set_RM (v : Nat) (Q : PUnit → Nat → Nat → Prop) (r s : Nat) :
    wp (set v : RM PUnit) Q E r s = Q ⟨⟩ r v := rfl

@[distill] theorem wrp_read_RM {Q : Nat → Nat → Nat → Nat → Prop} :
    (fun r s => ∀ x, PureRefinement r x True Eq → Q r x r s) ⊑ wrp γ (read : RM Nat) (read : RM Nat) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro r s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_read_RM] at h ⊢
  rw [Concretization.post, iSup_apply, iSup_apply]
  simp only [iSup_prop_eq_exists, meet_apply, meet_prop_eq_and, Concretization.id, id_eq]
  exact ⟨r, h.1 r (PureRefinement.of_rel rfl), h.2⟩

@[distill] theorem wrp_get_RM {Q : Nat → Nat → Nat → Nat → Prop} :
    (fun r s => ∀ x, PureRefinement s x True Eq → Q s x r s) ⊑ wrp γ (get : RM Nat) (get : RM Nat) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro r s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_get_RM] at h ⊢
  rw [Concretization.post, iSup_apply, iSup_apply]
  simp only [iSup_prop_eq_exists, meet_apply, meet_prop_eq_and, Concretization.id, id_eq]
  exact ⟨s, h.1 s (PureRefinement.of_rel rfl), h.2⟩

@[distill] theorem wrp_set_RM (v w : Nat) {Q : PUnit → PUnit → Nat → Nat → Prop} :
    (fun r _ => PureRefinement v w True Eq ∧ Q ⟨⟩ ⟨⟩ r v) ⊑ wrp γ (set v : RM PUnit) (set w : RM PUnit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro r s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_set_RM] at h ⊢
  obtain ⟨⟨hv, hq⟩, ha⟩ := h
  cases (hv trivial : v = w)
  rw [Concretization.post, iSup_apply, iSup_apply]
  simp only [iSup_prop_eq_exists, meet_apply, meet_prop_eq_and, Concretization.id, id_eq]
  exact ⟨⟨⟩, hq, ha⟩

@[distill] theorem wrp_pure_unit_RM {Q : Unit → Unit → Nat → Nat → Prop} :
    Q () () ⊑ wrp γ (pure () : RM Unit) (pure () : RM Unit) Q E :=
  wrp_pure () ()

end

attribute [distill] wrp_bind
attribute [distill_pure low] DistillBench.State.abs_refl
attribute [distill_pure] DistillBench.State.abs_add DistillBench.State.abs_sub

def step : RM Unit := do
  let r ← read
  let s ← get
  set (s + r)
  let s ← get
  set (s - r)

def loop (n : Nat) : RM Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

end DistillBench.ReaderState
