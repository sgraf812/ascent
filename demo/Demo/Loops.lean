import Demo.Structure

/-!
# Loops of a block table

The rules of this file turn a block loop into a structured loop step by step, on the table. Each
rule takes as a premise the refinement of the cells it moves, with an exception relation that names
the labels a cell may jump to, so the run that applies the rule refines the cells and proves their
jump targets at once. `refines_cfgLoop_self` is the last step: a table of one cell that jumps only
to itself is a `repeat'` loop.
-/

open Std.WP Lean.Order Ascent

namespace Ascent.Kraken

section
variable {σ α : Type}

theorem wp_tryCatch_block (x : BlockM σ α) (h : CfgLabel → BlockM σ α) (Q : α → σ → Prop)
    (E : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (tryCatch x h) Q E s = wp x Q (fun l => wp (h l) Q E, E.2) s := by
  rw [wp_BlockM_eq, wp_BlockM_eq]
  show (match (ExceptT.tryCatch x h).run.run s with
    | none => False | some (.ok a, st') => Q a st' | some (.error e, st') => E.1 e st') = _
  simp only [ExceptT.tryCatch, ExceptT.run_mk, StateT.run_bind]
  rw [show StateT.run x s = x.run.run s from rfl]
  rcases hx : x.run.run s with _ | ⟨l | a, s'⟩
  · rfl
  · simp only [UB.some_bind]
    rw [wp_BlockM_eq]
    rfl
  · rfl

end

/-- The loop of a cell `ab` that jumps only to itself: the cell runs again on its jump and the loop
ends when the cell falls through. -/
noncomputable def selfLoop {σ : Type} (ab : BlockM σ Unit) : BlockM σ Unit :=
  FixLoop.mk.forIn PUnit.unit fun _ _ =>
    tryCatch (ab >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun _ => pure (ForInStep.yield PUnit.unit))

section
variable {Cσ Aσ : Type} (view : Cσ → Aσ)

theorem refines_cfgLoop_self {b : BlockM Cσ Unit} {ab : BlockM Aσ Unit} {L : Label}
    {next : CfgLabel → CfgLabel} {I : Cσ → Prop}
    (hb : ⦃I⦄ b ⪯[Concretization.ofStateRepr view] ab
      ⦃fun _ _ => I; (fun l l' t => l = .label L ∧ l' = l ∧ I t, estack⟨⟩)⦄)
    (hnext : next (.label L) = .exit) :
    ⦃I⦄ (cfgLoop (Table.get [(.label L, b)]) next (.label L)) ⪯[Concretization.ofStateRepr view]
      (selfLoop ab) ⦃fun _ _ => I; (fun l l' t => l = l' ∧ I t, estack⟨⟩)⦄ := by
  have hget : Table.get [(CfgLabel.label L, b)] (.label L) = b := by simp [Table.get, List.lookup]
  generalize htbl : Table.get [(CfgLabel.label L, b)] = tbl at hget ⊢
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred] at hs
  obtain ⟨hI, hw⟩ := hs
  unfold selfLoop at hw
  have := FixLoop.forIn_induct (m := BlockM Aσ) (β := PUnit)
    (fun _ _ => tryCatch (ab >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun _ => pure (ForInStep.yield PUnit.unit)))
    (fun g => ∀ s, I s → wp (g PUnit.unit) Qa Ea (view s) →
      wp (cfgLoop tbl next (.label L))
        ((Concretization.ofStateRepr view).post (fun _ _ => I) Qa)
        (EPostsConcretization.ePosts (Concretization.ofStateRepr view)
          (fun l l' t => l = l' ∧ I t, estack⟨⟩) Ea) s)
    (admissible_pi _ fun s => admissible_pi _ fun _ =>
      admissible_apply (fun _ u => wp u Qa Ea (view s) → _) PUnit.unit
        (admissible_wp_imp _ Ea (view s) _)) ?_
  · exact this s hI hw
  intro g ih s hI hw
  simp only [FixLoop.step, WPMonadExact.wp_bind_eq, wp_tryCatch_block, WPMonadExact.wp_pure_eq] at hw
  rw [wp_cfgLoop _ _ _ _ _ (by simp), hget, hnext, wp_cfgLoop_exit_fn]
  have hb' := wrp_transport hb.le_wrp (fun _ => Qa PUnit.unit)
    (fun _ m => wp (g PUnit.unit) Qa Ea m, Ea.2) s
    (by simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]; exact ⟨hI, hw⟩)
  refine WP.wp_monotone (x := b) ?_ ?_ s hb'
  · intro u t ht
    rw [Concretization.post_pi] at ht ⊢
    obtain ⟨_, hIt, hq⟩ := ht
    exact ⟨PUnit.unit, hIt, hq⟩
  · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l t ht
    rw [Concretization.post_pi] at ht
    obtain ⟨l', ⟨rfl, rfl, hIt⟩, hq⟩ := ht
    simp only [cfgEPosts, reduceCtorEq, ↓reduceIte]
    exact ih t hIt hq

end

end Ascent.Kraken
