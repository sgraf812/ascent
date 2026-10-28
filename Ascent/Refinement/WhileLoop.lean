import Ascent.UB.WhileLoop
import Ascent.UB.StateT

/-!
# Refinement of `while` loops

`refines_whileLoop` reduces the refinement of two loops under `Concretization.ofStateRel J` to
the refinement of their bodies, given that the conditions agree on `J`-related states and that a
variant `μ` decreases on the abstract body.
-/

open Std.WP Lean.Order Ascent

theorem wp_whileLoop {σ} (cond : σ → Bool) (body : StateT σ UB Unit)
    (Q : Unit → σ → Prop) (E : EStack⟨⟩) (s : σ) :
    wp (whileLoop cond body) Q E s
      = if cond s then wp body (fun _ s' => wp (whileLoop cond body) Q E s') E s else Q () s := by
  rw [whileLoop, StateT.wp_apply_eq, StateT.run, loopFix]
  simp only [wp_ite, UB.wp_bind_eq, UB.wp_pure_eq, StateT.wp_apply_eq, StateT.run]

theorem refines_whileLoop {Aσ Cσ : Type} (J : Cσ → Aσ → Prop)
    (ccond : Cσ → Bool) (cbody : StateT Cσ UB Unit)
    (acond : Aσ → Bool) (abody : StateT Aσ UB Unit)
    (μ : Aσ → Nat)
    (hcond : ∀ cs as, J cs as → ccond cs = acond as)
    (hbody : ⦃(⊤ : Cσ → Prop)⦄ cbody ⪯[Concretization.ofStateRel J] abody ⦃fun _ _ => ⊤⦄)
    (hμ : ∀ (E : EStack⟨⟩) as, acond as = true → wp abody (fun _ _ => True) E as →
        wp abody (fun _ as' => μ as' < μ as) E as) :
    ⦃(⊤ : Cσ → Prop)⦄ (whileLoop ccond cbody) ⪯[Concretization.ofStateRel J] (whileLoop acond abody)
      ⦃fun _ _ => ⊤⦄ := by
  refine ⟨wrp_intro fun Q E => ?_⟩
  intro cs hcs
  simp only [_root_.top_meet, Concretization.ofStateRel_pred] at hcs
  obtain ⟨as, hJ, hwp⟩ := hcs
  suffices H : ∀ n as cs, μ as < n → J cs as → wp (whileLoop acond abody) Q E as →
      wp (whileLoop ccond cbody) ((Concretization.ofStateRel J).post (fun _ _ => ⊤) Q) E cs by
    exact H (μ as + 1) as cs (Nat.lt_succ_self _) hJ hwp
  intro n
  induction n with
  | zero => intro as cs hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro as cs hlt hJ hwp
    rw [wp_whileLoop] at hwp
    rw [wp_whileLoop]
    have hcc := hcond cs as hJ
    by_cases hc : acond as = true
    · rw [ite_eq_left hc] at hwp
      have hcct : ccond cs = true := by rw [hcc]; exact hc
      rw [ite_eq_left hcct]
      have hsucc : wp abody (fun _ _ => True) E as :=
        WP.wp_monotone_post (x := abody) (fun _ _ _ => trivial) as hwp
      have hcomb := wp_and_StateT abody _ _ E as hwp (hμ E as hc hsucc)
      have hcb := (wrp_transport hbody.le_wrp (fun _ as' => wp (whileLoop acond abody) Q E as' ∧ μ as' < μ as) E)
        cs (by simp only [_root_.top_meet, Concretization.ofStateRel_pred]; exact ⟨as, hJ, hcomb⟩)
      simp only [Concretization.ofStateRel_post_top] at hcb
      refine WP.wp_monotone_post (x := cbody) ?_ cs hcb
      intro _ cs' hpost'
      obtain ⟨_, as', hJ', hwp', hlt'⟩ := hpost'
      exact ih as' cs' (Nat.lt_of_lt_of_le hlt' (Nat.lt_succ_iff.mp hlt)) hJ' hwp'
    · have hcf : acond as = false := by simp only [Bool.not_eq_true] at hc; exact hc
      rw [ite_eq_right (by rw [hcf]; simp)] at hwp
      have hccf : ccond cs = false := by rw [hcc]; exact hcf
      rw [ite_eq_right (by rw [hccf]; simp)]
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
