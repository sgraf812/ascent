import Ascent.Refinement
import Ascent.UB.StateT

/-!
# Stutter and read steps in `StateT σ UB`

A concrete step with no abstract counterpart is a stutter step. Under `ofStateRepr f` it is sound
when it leaves `f` of the state unchanged (`wrp_stutter`). A concrete read in tail position
abstracts to `pure av` when the read leaves the abstract view unchanged (`wrp_read` under
`ofStateRepr f`, `wrp_read_rel` under `ofStateRel J`). The specs of the `@[ascend]` database are
instances of these lemmas.
-/

open Std.WP Lean.Order Ascent Ascent.Concretization

namespace Ascent

variable {Cσ Aσ CV CV₂ AV : Type}

theorem wrp_stutter (f : Cσ → Aσ) (c₁ : StateT Cσ UB CV) (c₂ : CV → StateT Cσ UB CV₂)
    (a : StateT Aσ UB AV) (Q : CV₂ → AV → Cσ → Prop) (E : EStack⟨⟩) :
    (fun s => wp c₁ (fun v s' => f s' = f s ∧ wrp (ofStateRepr f) (c₂ v) a Q E s') E s)
      ⊑ wrp (ofStateRepr f) (c₁ >>= c₂) a Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and] at hs
  obtain ⟨h, ha⟩ := hs
  rw [wp_bind_StateT]
  refine WP.wp_monotone_post (x := c₁) ?_ s h
  rintro v s' ⟨hf, hw⟩
  refine wrp_transport (P := wrp (ofStateRepr f) (c₂ v) a Q E) PartialOrder.rel_refl Qa Ea s' ?_
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at ha ⊢
  rw [hf]
  exact ⟨hw, ha⟩

theorem wrp_read (f : Cσ → Aσ) (c : StateT Cσ UB CV) (av : AV) (Q : CV → AV → Cσ → Prop)
    (E : EStack⟨⟩) :
    (fun s => wp c (fun v s' => f s' = f s ∧ Q v av s') E s)
      ⊑ wrp (ofStateRepr f) c (pure av : StateT Aσ UB AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and] at hs
  obtain ⟨h, ha⟩ := hs
  simp only [ofStateRepr_pred, StateT.wp_apply_eq, StateT.run_pure, UB.wp_pure_eq] at ha
  refine WP.wp_monotone_post (x := c) ?_ s h
  rintro v s' ⟨hf, hq⟩
  simp only [post_pi, ofStateRepr_pred]
  exact ⟨av, hq, by rw [hf]; exact ha⟩

theorem wrp_read_rel (J : Cσ → Aσ → Prop) (c : StateT Cσ UB CV) (av : AV)
    (Q : CV → AV → Cσ → Prop) (E : EStack⟨⟩) :
    (⨅ as, (J · as) ⇨ wp c (fun v s' => J s' as ∧ Q v av s') E)
      ⊑ wrp (ofStateRel J) c (pure av : StateT Aσ UB AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, iInf_apply, himp_apply,
    iInf_prop_eq_forall, himp_prop_eq_imp] at hs
  obtain ⟨h, as, hJ, ha⟩ := hs
  simp only [StateT.wp_apply_eq, StateT.run_pure, UB.wp_pure_eq] at ha
  refine WP.wp_monotone_post (x := c) ?_ s (h as hJ)
  rintro v s' ⟨hJ', hq⟩
  simp only [post_pi, ofStateRel_pred]
  exact ⟨av, hq, as, hJ', ha⟩

end Ascent
