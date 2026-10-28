import Ascent.UB.WhileLoop
import Ascent.UB.StateT

/-!
# Refinement of `while` loops

`Refinement.whileLoop` is fixpoint induction over the abstract loop. To refine
`whileLoop acond abody`, it suffices to refine one unfolding of the abstract loop in which the
recursive call is an arbitrary program `f` that the concrete loop refines. The concrete side
unfolds by `whileLoop_unfold`. The concretization must preserve suprema, because the abstract
loop is the supremum of its finite unfoldings.

`refines_whileLoop` is the lockstep instance under `Concretization.ofStateRel J`: the conditions
agree on `J`-related states, and the bodies refine each other.
-/

open Std.WP Lean.Order Ascent

theorem Refinement.whileLoop {Cσ Aσ : Type} {γ : Concretization (Cσ → Prop) (Aσ → Prop)}
    (hγ : ∀ (ι : Type) (X : ι → Aσ → Prop), γ.pred (iSup X) ⊑ iSup fun i => γ.pred (X i))
    {P : Cσ → Prop} {Q : Unit → Unit → Cσ → Prop}
    {ccond : Cσ → Bool} {cbody : StateT Cσ UB Unit} {acond : Aσ → Bool} {abody : StateT Aσ UB Unit}
    (h : ∀ f : StateT Aσ UB Unit, ⦃P⦄ (_root_.whileLoop ccond cbody) ⪯[γ] f ⦃Q⦄ →
      ⦃P⦄ (get >>= fun cs =>
          if ccond cs then cbody >>= fun _ => _root_.whileLoop ccond cbody else pure ())
        ⪯[γ] (get >>= fun as => if acond as then abody >>= fun _ => f else pure ()) ⦃Q⦄) :
    ⦃P⦄ (_root_.whileLoop ccond cbody) ⪯[γ] (_root_.whileLoop acond abody) ⦃Q⦄ := by
  refine loopFix.fixpoint_induct acond abody
    (fun f => ⦃P⦄ (_root_.whileLoop ccond cbody) ⪯[γ] (show StateT Aσ UB Unit from f) ⦃Q⦄) ?_ ?_
  · intro ch hch hall
    refine ⟨wrp_intro fun Qa Ea => ?_⟩
    refine PartialOrder.rel_trans (meet_mono_right (γ.pred_mono (wp_csup_StateT hch Qa Ea))) ?_
    refine PartialOrder.rel_trans (meet_mono_right (hγ _ _)) ?_
    refine PartialOrder.rel_trans (meet_iSup_le _ _) ?_
    exact iSup_le _ _ fun f => wrp_transport (hall f.1 f.2).le_wrp Qa Ea
  · intro f hf
    have := h f hf
    rw [← whileLoop_unfold, ← loopStep_eq] at this
    exact this

theorem refines_whileLoop {Aσ Cσ : Type} (J : Cσ → Aσ → Prop)
    (ccond : Cσ → Bool) (cbody : StateT Cσ UB Unit)
    (acond : Aσ → Bool) (abody : StateT Aσ UB Unit)
    (hcond : ∀ cs as, J cs as → ccond cs = acond as)
    (hbody : ⦃(⊤ : Cσ → Prop)⦄ cbody ⪯[Concretization.ofStateRel J] abody ⦃fun _ _ => ⊤⦄) :
    ⦃(⊤ : Cσ → Prop)⦄ (whileLoop ccond cbody) ⪯[Concretization.ofStateRel J] (whileLoop acond abody)
      ⦃fun _ _ => ⊤⦄ := by
  refine Refinement.whileLoop (fun _ X => Concretization.ofStateRel_pred_iSup J X) fun f hf => ?_
  refine ⟨wrp_intro fun Qa E => ?_⟩
  intro cs hcs
  simp only [_root_.top_meet, Concretization.ofStateRel_pred] at hcs
  obtain ⟨as, hJ, hwp⟩ := hcs
  rw [wp_loopStep] at hwp
  rw [wp_loopStep, hcond cs as hJ]
  split
  · next hc =>
    rw [ite_eq_left hc] at hwp
    have hcb := (wrp_transport hbody.le_wrp (fun _ as' => wp f Qa E as') E) cs
      (by simp only [_root_.top_meet, Concretization.ofStateRel_pred]; exact ⟨as, hJ, hwp⟩)
    simp only [Concretization.ofStateRel_post_top] at hcb
    refine WP.wp_monotone_post (x := cbody) ?_ cs hcb
    rintro _ cs' ⟨_, as', hJ', hwp'⟩
    exact (wrp_transport hf.le_wrp Qa E) cs'
      (by simp only [_root_.top_meet, Concretization.ofStateRel_pred]; exact ⟨as', hJ', hwp'⟩)
  · next hc =>
    rw [ite_eq_right hc] at hwp
    simp only [Concretization.ofStateRel_post_top]
    exact ⟨(), as, hJ, hwp⟩

theorem refines_relEq_self {σ α} (P : σ → Prop) (a : StateT σ UB α) :
    ⦃P⦄ a ⪯[Concretization.ofStateRel (Eq : σ → σ → Prop)] a ⦃fun cv av => ⌜cv = av⌝⦄ := by
  refine ⟨wrp_intro fun Q E => ?_⟩
  intro cs hcs
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRel_pred] at hcs
  obtain ⟨-, as, rfl, hwp⟩ := hcs
  refine WP.wp_monotone_post (x := a) (post := Q) ?_ cs hwp
  intro cv cs' hq
  simp only [Concretization.post_eq, Concretization.ofStateRel_pred]
  exact ⟨cs', rfl, hq⟩
