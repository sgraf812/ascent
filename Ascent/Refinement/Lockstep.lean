import Ascent.FixLoop
import Ascent.Refinement
import Ascent.Demonic.StateT
import Ascent.Tactic.VCGen.Command

/-!
# Lockstep loops over `ExceptT ε (StateT σ Demonic)`

`wrp_forIn_lockstep` refines a `FixLoop` loop to a `FixLoop` loop of the abstract program under a
state representation `view`: the relation `R c t a` between the concrete loop value `c`, the
concrete state `t` and the abstract loop value `a` holds at the start, and one iteration of the two
bodies keeps it, both continue or both stop. The post of a body matches on the concrete step only
and names the abstract step through `∃`: a concrete `.yield c` is related to an abstract
`.yield a` with `R c t a`, a concrete `.done c` to an abstract `.done a` with `Q c a t`. The relation comes before the equation of the steps, so `a` is solved before the abstract step is assigned. An applied
post reduces on the concrete constructor, and the abstract step is a witness, which `ascend`
synthesizes. `stepRel_iff` states the post as a `match` on both steps. The proof is fixpoint
induction over the abstract loop.

Abstract values come from witnesses and value rules: the loop leaves `pure (.yield c)` and
`pure (.done c)` refine `pure ra` for any abstract step `ra` (`wrp_pure_step`).
-/

open Std.WP Lean.Order Ascent
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent

theorem admissible_wp_imp {ε σ α : Type} (Q : α → σ → Prop) (E : (ε → σ → Prop) × EStack⟨⟩)
    (s : σ) (R : Prop) : admissible fun u : ExceptT ε (StateT σ Demonic) α => wp u Q E s → R := by
  intro ch hch hall hw
  have := WPCont.wp_csup (Prog := ExceptT ε (StateT σ Demonic) α) hch Q E s hw
  simp only [iSup_apply, iSup_prop_eq_exists] at this
  obtain ⟨⟨u, hu⟩, hwu⟩ := this
  exact hall u hu hwu

@[spec_invariant_type, simp, grind =]
def LockstepInvariant (βc σ βa : Type) := βc → σ → βa → Prop

theorem stepRel_iff {βc βa σ : Type} (R : βc → σ → βa → Prop) (Q : βc → βa → σ → Prop)
    (rc : ForInStep βc) (ra : ForInStep βa) (t : σ) :
    (match rc with
      | .yield c => ∃ a, R c t a ∧ ra = .yield a
      | .done c => ∃ a, Q c a t ∧ ra = .done a) ↔
    (match rc, ra with
      | .yield c, .yield a => R c t a
      | .done c, .done a => Q c a t
      | _, _ => False) := by
  cases rc <;> cases ra <;> simp

section
variable {εc εa σc σa : Type} {view : σc → σa} {E : (εc → εa → σc → Prop) × EStack⟨⟩}

theorem wrp_forIn_lockstep {βc βa : Type} (R : LockstepInvariant βc σc βa) (cinit : βc) (ainit : βa)
    {fc : Unit → βc → ExceptT εc (StateT σc Demonic) (ForInStep βc)}
    {fa : βa → ExceptT εa (StateT σa Demonic) (ForInStep βa)}
    {Q : βc → βa → σc → Prop}
    (hbody : ∀ c a, (fun t => R c t a) ⊑
      wrp (ofStateRepr view) (fc () c) (fa a) (fun rc ra t => match rc with
        | .yield c' => ∃ a', R c' t a' ∧ ra = .yield a'
        | .done c' => ∃ a', Q c' a' t ∧ ra = .done a') E) :
    (fun t => R cinit t ainit) ⊑ wrp (ofStateRepr view) (FixLoop.mk.forIn cinit fc)
      (FixLoop.mk.forIn ainit fun _ a => fa a) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at ht
  haveI : Nonempty βa := ⟨ainit⟩
  have key := FixLoop.forIn_induct (fun _ a => fa a)
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
      refine ⟨hR, WP.wp_monotone_post (x := fa a) ?_ (view t) hw⟩
      intro r m hr
      cases r <;> simp only [WPMonadExact.wp_pure_eq] at hr ⊢ <;> exact hr)
  refine WP.wp_monotone_post (x := fc () c) ?_ t hb
  intro rc t' h'
  rw [Concretization.post_pi] at h'
  obtain ⟨ra, hrel, hq⟩ := h'
  simp only [ofStateRepr_pred] at hq
  cases rc with
  | done c' =>
    obtain ⟨a', hrel, rfl⟩ := hrel
    simp only [WPMonadExact.wp_pure_eq]
    rw [Concretization.post_pi]
    exact ⟨_, hrel, hq⟩
  | yield c' =>
    obtain ⟨a', hrel, rfl⟩ := hrel
    exact ih _ _ t' hrel hq

theorem wrp_forIn_lockstep_bind {βc βa γc γa : Type} (R D : LockstepInvariant βc σc βa) (cinit : βc)
    (ainit : βa) {fc : Unit → βc → ExceptT εc (StateT σc Demonic) (ForInStep βc)}
    {fa : βa → ExceptT εa (StateT σa Demonic) (ForInStep βa)} {kc : βc → ExceptT εc (StateT σc Demonic) γc}
    {ka : βa → ExceptT εa (StateT σa Demonic) γa} {Q : γc → γa → σc → Prop}
    (hbody : ∀ c a, (fun t => R c t a) ⊑
      wrp (ofStateRepr view) (fc () c) (fa a) (fun rc ra t => match rc with
        | .yield c' => ∃ a', R c' t a' ∧ ra = .yield a'
        | .done c' => ∃ a', D c' t a' ∧ ra = .done a') E)
    (hk : ∀ c a, (fun t => D c t a) ⊑ wrp (ofStateRepr view) (kc c) (ka a) Q E) :
    (fun t => R cinit t ainit) ⊑ wrp (ofStateRepr view) (FixLoop.mk.forIn cinit fc >>= kc)
      ((FixLoop.mk.forIn ainit fun _ a => fa a) >>= ka) Q E := by
  have h := wrp_forIn_lockstep (view := view) (Q := fun c a t => D c t a) R cinit ainit hbody
  exact PartialOrder.rel_trans (PartialOrder.rel_trans h (wrp_mono_post (fun c a => hk c a))) wrp_bind

theorem wrp_forIn_lockstep_pure {βc βa γa : Type} (R D : LockstepInvariant βc σc βa) (cinit : βc)
    (ainit : βa) {fc : Unit → βc → ExceptT εc (StateT σc Demonic) (ForInStep βc)}
    {fa : βa → ExceptT εa (StateT σa Demonic) (ForInStep βa)} {ka : βa → ExceptT εa (StateT σa Demonic) γa}
    {Q : βc → γa → σc → Prop}
    (hbody : ∀ c a, (fun t => R c t a) ⊑
      wrp (ofStateRepr view) (fc () c) (fa a) (fun rc ra t => match rc with
        | .yield c' => ∃ a', R c' t a' ∧ ra = .yield a'
        | .done c' => ∃ a', D c' t a' ∧ ra = .done a') E)
    (hk : ∀ c a, (fun t => D c t a) ⊑
      wrp (ofStateRepr view) (pure c : ExceptT εc (StateT σc Demonic) βc) (ka a) Q E) :
    (fun t => R cinit t ainit) ⊑ wrp (ofStateRepr view) (FixLoop.mk.forIn cinit fc)
      ((FixLoop.mk.forIn ainit fun _ a => fa a) >>= ka) Q E := by
  simpa only [bind_pure] using wrp_forIn_lockstep_bind (kc := pure) R D cinit ainit hbody hk

variable {βc βa : Type} {Q : ForInStep βc → ForInStep βa → σc → Prop}

@[ascend] theorem wrp_pure_step (c : ForInStep βc) (a : ForInStep βa) :
    (fun t => Q c a t) ⊑ wrp (ofStateRepr view)
      (pure c : ExceptT εc (StateT σc Demonic) (ForInStep βc))
      (pure a : ExceptT εa (StateT σa Demonic) (ForInStep βa)) Q E :=
  wrp_pure (Q := Q) c a

end

end Ascent
