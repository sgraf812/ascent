import Cases.Setup.State

/-!
# `AddSubCancelDeep`: a deep transformer stack

The mirror of the `vcgen` case `AddSubCancelDeep`: the loop of `AddSubCancel` in a stack of three
`ExceptT` transformers, a `ReaderT` and two `StateT` over `Demonic`, in the order of the `vcgen`
case. The inner `ExceptT Nat` and `ExceptT Unit` have the predicates of their depth, so the
exception relation has the components `String → String → DPred`, `Nat → Nat → Nat → Unit → Prop`
and `Unit → Unit → Unit → Prop`. The rules for `getThe Nat` and `set` reach through all
transformers in one step. The family stresses goals with three state arguments and an exception
relation with three components at three depths.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.AddSubCancelDeep

instance {ρ : Type u} {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m Pred EPosts] :
    WPMonadExact (ReaderT ρ m) (ρ → Pred) EPosts where
  wp_pure_le a := fun post epost r => by
    rw [ReaderT.wp_apply_eq]
    exact WPMonadExact.wp_pure_le (m := m) a (fun a => post a r) epost
  wp_bind_le x f := fun post epost r => by
    simp only [ReaderT.wp_apply_eq]
    exact WPMonadExact.wp_bind_le (m := m) (x.run r) (fun a => (f a).run r) (fun a => post a r) epost

-- The exception relations of `DM` have an `Assertion` instance of more than 128 nodes.
set_option synthInstance.maxSize 1024

abbrev DM := ExceptT String <| ReaderT String <| ExceptT Nat <| StateT Nat <| ExceptT Unit <|
  StateT Unit Demonic

abbrev DPred := String → Nat → Unit → Prop

abbrev γd : Concretization DPred DPred := Concretization.id DPred

abbrev DER := (String → String → DPred) × (Nat → Nat → Nat → Unit → Prop) ×
  (Unit → Unit → Unit → Prop) × EStack⟨⟩

abbrev DEPosts := (String → DPred) × (Nat → Nat → Unit → Prop) × (Unit → Unit → Prop) × EStack⟨⟩

section
variable {E : DER}

theorem wp_getThe_DM (Q : Nat → DPred) (Ea : DEPosts) (r : String) (s : Nat) (u : Unit) :
    wp (getThe Nat : DM Nat) Q Ea r s u = Q s r s u := rfl

theorem wp_set_DM (v : Nat) (Q : PUnit → DPred) (Ea : DEPosts) (r : String) (s : Nat) (u : Unit) :
    wp (set v : DM PUnit) Q Ea r s u = Q ⟨⟩ r v u := rfl

@[distill] theorem wrp_getThe_DM {Q : Nat → Nat → DPred} :
    (fun r s u => ∀ x, PureRefinement s x True Eq → Q s x r s u)
      ⊑ wrp γd (getThe Nat : DM Nat) (getThe Nat : DM Nat) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro r s u h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_getThe_DM] at h ⊢
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
    Concretization.id, id_eq]
  exact ⟨s, h.1 s (PureRefinement.of_rel rfl), h.2⟩

@[distill] theorem wrp_set_DM (v w : Nat) {Q : PUnit → PUnit → DPred} :
    (fun r _ u => PureRefinement v w True Eq ∧ Q ⟨⟩ ⟨⟩ r v u)
      ⊑ wrp γd (set v : DM PUnit) (set w : DM PUnit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro r s u h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_set_DM] at h ⊢
  obtain ⟨⟨hv, hq⟩, ha⟩ := h
  cases (hv trivial : v = w)
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
    Concretization.id, id_eq]
  exact ⟨⟨⟩, hq, ha⟩

@[distill] theorem wrp_pure_unit_DM {Q : Unit → Unit → DPred} :
    Q () () ⊑ wrp γd (pure () : DM Unit) (pure () : DM Unit) Q E :=
  wrp_pure () ()

end

attribute [distill] wrp_bind
attribute [distill_pure low] abs_refl
attribute [distill_pure] abs_add abs_sub

def step (v : Nat) : DM Unit := do
  let s ← getThe Nat
  set (s + v)
  let s ← getThe Nat
  set (s - v)

def loop (n : Nat) : DM Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

end DistillBench.AddSubCancelDeep
