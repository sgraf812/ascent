import Distillery.Demonic.StateT
import Distillery.PureRefinement
import Distillery.Tactic.VCGen.Command

/-!
# An exception layer below a `ReaderT`

In `M := ReaderT String (ExceptT Nat (StateT Nat Demonic))`, the exception layer of `ExceptT Nat`
has the predicates `Nat → Prop` of its depth, not the predicates `String → Nat → Prop` of `M`. The
exception relation of `M` is `(Nat → Nat → Nat → Prop) × EStack⟨⟩`, and its aligned layer
concretizes by `LayerConcretization.layer`, the identity on `Nat → Prop`. The program throws at the
inner layer and distills to the same `throwThe`. The test pins the `EPostsConcretization` instance of
an aligned layer at an inner depth, in `Distillery/EPostsConcretization.lean`.
-/

open Std.WP Lean.Order Distillery

namespace InnerExceptionTest

abbrev M := ReaderT String (ExceptT Nat (StateT Nat Demonic))

abbrev γ : Concretization (String → Nat → Prop) (String → Nat → Prop) := Concretization.id _

abbrev ER := (Nat → Nat → Nat → Prop) × EStack⟨⟩

theorem wp_throwThe_M {α : Type} (e : Nat) (Q : α → String → Nat → Prop)
    (E : (Nat → Nat → Prop) × EStack⟨⟩) (r : String) (s : Nat) :
    wp (throwThe Nat e : M α) Q E r s = E.1 e s := rfl

@[distill] theorem wrp_throwThe_M {α : Type} (e : Nat) {Q : α → α → String → Nat → Prop} {E : ER} :
    (fun _ s => E.1 e e s) ⊑ wrp γ (throwThe Nat e : M α) (throwThe Nat e : M α) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro r s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_throwThe_M] at h ⊢
  show (Concretization.id (Nat → Prop)).post E.1 Ea.1 e s
  rw [Concretization.post_pi]
  exact ⟨e, h.1, h.2⟩

def prog : M Unit := throwThe Nat 3

distill_def progA : M Unit from
  ⦃fun _ _ => True⦄ prog ⪯[γ] progA ⦃fun _ _ _ _ => True; ((fun e e' _ => e = e'), estack⟨⟩)⦄
  distill [prog]

/--
info: def InnerExceptionTest.progA : M Unit :=
MonadExceptOf.throw 3
-/
#guard_msgs in
#print progA

end InnerExceptionTest
