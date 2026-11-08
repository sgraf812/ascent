import Ascent.FixLoop
import Ascent.Refinement
import Ascent.UB.StateT

/-!
# Lockstep loops over `ExceptT ε (StateT σ UB)`

`wrp_forIn_lockstep` refines a `FixLoop` loop to a `FixLoop` loop of the abstract program under a
state representation `view`: the relation `R c t a` between the concrete loop value `c`, the
concrete state `t` and the abstract loop value `a` holds at the start, and one iteration of the two
bodies keeps it, both continue or both stop. The post of a body is a `match` on the two steps, so
an applied post reduces to `R` or to `Q` on constructors. The proof is fixpoint induction over the
abstract loop.
-/

open Std.WP Lean.Order Ascent
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent

theorem admissible_wp_imp {ε σ α : Type} (Q : α → σ → Prop) (E : (ε → σ → Prop) × EStack⟨⟩)
    (s : σ) (R : Prop) : admissible fun u : ExceptT ε (StateT σ UB) α => wp u Q E s → R := by
  intro ch hch hall hw
  have := WPCont.wp_csup (Prog := ExceptT ε (StateT σ UB) α) hch Q E s hw
  simp only [iSup_apply, iSup_prop_eq_exists] at this
  obtain ⟨⟨u, hu⟩, hwu⟩ := this
  exact hall u hu hwu

section
variable {εc εa σc σa : Type} {view : σc → σa} {E : (εc → εa → σc → Prop) × EStack⟨⟩}

theorem wrp_forIn_lockstep {βc βa : Type} (R : βc → σc → βa → Prop) (cinit : βc) (ainit : βa)
    {fc : Unit → βc → ExceptT εc (StateT σc UB) (ForInStep βc)}
    {fa : Unit → βa → ExceptT εa (StateT σa UB) (ForInStep βa)}
    {Q : βc → βa → σc → Prop}
    (hbody : ∀ c a, (fun t => R c t a) ⊑
      wrp (ofStateRepr view) (fc () c) (fa () a) (fun rc ra t => match rc, ra with
        | .yield c', .yield a' => R c' t a'
        | .done c', .done a' => Q c' a' t
        | _, _ => False) E) :
    (fun t => R cinit t ainit) ⊑ wrp (ofStateRepr view) (FixLoop.mk.forIn cinit fc)
      (FixLoop.mk.forIn ainit fa) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at ht
  haveI : Nonempty βa := ⟨ainit⟩
  have key := FixLoop.forIn_induct fa
    (fun g => ∀ c a t, R c t a → wp (g a) Qa Ea (view t) →
      wp (FixLoop.mk.forIn c fc) ((ofStateRepr view).post Q Qa)
        (EPostsConcretization.ePosts (ofStateRepr view) E Ea) t)
    (admissible_pi _ fun _ => admissible_pi _ fun a => admissible_pi _ fun t =>
      admissible_pi _ fun _ =>
        admissible_apply (fun _ u => wp u Qa Ea (view t) → _) a
          (admissible_wp_imp _ Ea (view t) _)) ?_
  · exact key cinit ainit t ht.1 ht.2
  intro g ih c a t hR hw
  rw [FixLoop.forIn_eq, WPMonadExact.wp_bind_eq]
  simp only [FixLoop.step, WPMonadExact.wp_bind_eq] at hw
  have hb := wrp_transport (hbody c a)
    (fun r m => match r with | .done a' => Qa a' m | .yield a' => wp (g a') Qa Ea m) Ea t (by
      simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]
      refine ⟨hR, WP.wp_monotone_post (x := fa () a) ?_ (view t) hw⟩
      intro r m hr
      cases r <;> simp only [WPMonadExact.wp_pure_eq] at hr ⊢ <;> exact hr)
  refine WP.wp_monotone_post (x := fc () c) ?_ t hb
  intro rc t' h'
  rw [Concretization.post_pi] at h'
  obtain ⟨ra, hrel, hq⟩ := h'
  simp only [ofStateRepr_pred] at hq
  cases rc <;> cases ra <;> simp only at hrel
  · simp only [WPMonadExact.wp_pure_eq]
    rw [Concretization.post_pi]
    exact ⟨_, hrel, hq⟩
  · exact ih _ _ t' hrel hq

end

end Ascent
