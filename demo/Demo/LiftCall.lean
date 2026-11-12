import Demo.L1Rel
import Demo.Lift

/-!
# Calls with their registers lifted

`callL r k` is the call over the data memory alone, for the stack pointer `r` of the caller. It
requires the cell below `r`, hides the return slot, runs the abstract callee `k (r - 8)`, and
returns when `k` throws. The call rule refines `callA kT` to `callL r kL` from the refinement of the
callee `kT` to `kL` for every frame. The precondition of that refinement names the registers that
the callee reads, and its exit relation names the registers that the return keeps; the caller
continues with those facts alone, so the registers that the callee clobbers have no value.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Kraken

noncomputable def callL (r : BitVec 64) (k : BitVec 64 → BlockM DataMem Unit) : BlockM DataMem Unit := do
  modifyIf (fun m => (Mem.loadInt m (r - 8#64) 8).isSome = true) (hideSlot (r - 8#64))
  tryCatch (do k (r - 8#64); modifyIf (fun _ => False) id) fun _ => pure ()

theorem ThrowsOnly.callL {P : Int64 → DataMem → Prop} (r : BitVec 64) (k : BitVec 64 → BlockM DataMem Unit) :
    Ascent.ThrowsOnly P (callL r k) = True := eq_true fun Q E s hw => by
  simp only [Kraken.callL, WPMonadExact.wp_bind_eq, wp_modifyIf, BlockLoop.wp_tryCatch, wp_modifyIf_fun,
    WPMonadExact.wp_pure_eq] at hw ⊢
  exact hw

theorem tryCatch_callL_bind {β : Type} (r : BitVec 64) (k : BitVec 64 → BlockM DataMem Unit)
    (f : Unit → BlockM DataMem β) (h : Int64 → BlockM DataMem β) :
    tryCatch (callL r k >>= f) h = callL r k >>= fun u => tryCatch (f u) h := by
  apply BlockLoop.ext_wp <;> intro Q E s hw <;>
    simp only [Kraken.callL, WPMonadExact.wp_bind_eq, wp_modifyIf, BlockLoop.wp_tryCatch,
      wp_modifyIf_fun, wp_tryCatch_fun, WPMonadExact.wp_pure_eq] at hw ⊢ <;>
    exact hw

section
variable {Q : Unit → Unit → MachineData → Prop} {E : (Int64 → Int64 → MachineData → Prop) × EStack⟨⟩}

/-- A call of `kT` refines a call of `kL`, from the refinement of the callee for every frame. -/
theorem wrp_callA_callL {kT : BitVec 64 → BlockM MachineData Unit} {kL : BitVec 64 → BlockM DataMem Unit}
    {Pre Post : BitVec 64 → MachineData → Prop}
    (hk : ∀ r₀, ⦃Pre r₀⦄ (kT r₀) ⪯[ofStateRepr MachineData.dmem] (kL r₀)
      ⦃fun _ _ _ => False; (fun _ _ t => t.regs.get64 .rsp = r₀ + 8#64 ∧ Post r₀ t, estack⟨⟩)⦄)
    (r : BitVec 64) :
    (fun t => t.regs.get64 .rsp ≐ r ∧ Pre (r - 8#64) (hidePush r t) ∧
      ∀ t', t'.regs.get64 .rsp ≐ r → Post (r - 8#64) t' → Q () () t')
      ⊑ wrp (ofStateRepr MachineData.dmem) (callA kT) (callL r kL) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at ht
  obtain ⟨⟨hr, hpre, hQ⟩, hw⟩ := ht
  have hr : t.regs.get64 .rsp = r := hr trivial
  simp only [callL, WPMonadExact.wp_bind_eq, wp_modifyIf, BlockLoop.wp_tryCatch, wp_modifyIf_fun,
    WPMonadExact.wp_pure_eq] at hw
  obtain ⟨hm, hw⟩ := hw
  simp only [callA, WPMonadExact.wp_bind_eq, wp_peek, wp_modifyIf, BlockLoop.wp_tryCatch, wp_modifyIf_fun]
  rw [hr]
  refine ⟨hm, ?_⟩
  let Qa' : Unit → DataMem → Prop := fun _ _ => False
  let Ea' : (Int64 → DataMem → Prop) × EStack⟨⟩ := (fun _ m => Qa () m, Ea.2)
  have hc := wrp_transport (hk (r - 8#64)).le_wrp Qa' Ea' (hidePush r t)
    (by
      simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, hidePush_dmem]
      refine ⟨hpre, ?_⟩
      refine WP.wp_monotone (x := kL (r - 8#64)) ?_ ?_ _ hw
      · intro u m hm'; exact hm'.1
      · exact Prod.mk_le _ _ _ (fun _ _ h => h) PartialOrder.rel_refl)
  refine WP.wp_monotone (x := kT (r - 8#64)) ?_ ?_ _ hc
  · intro u t' ht'
    simp only [Concretization.post_pi, ofStateRepr_pred, Qa', and_false, exists_false] at ht'
  · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l t' ht'
    simp only [Concretization.post_pi, ofStateRepr_pred] at ht'
    obtain ⟨_, ⟨hrs, hpost⟩, hqa⟩ := ht'
    show t'.regs.get64 .rsp = r ∧ (ofStateRepr MachineData.dmem).post Q Qa () t'
    refine ⟨by rw [hrs, BitVec.sub_add_cancel], ?_⟩
    rw [Concretization.post_pi]
    exact ⟨(), hQ t' (PureRefinement.of_rel (by rw [hrs, BitVec.sub_add_cancel])) hpost, hqa⟩
theorem Refinement.mono_exit_dmem {CV AV : Type} {c : BlockM MachineData CV} {a : BlockM DataMem AV}
    {P : MachineData → Prop} {Q : CV → AV → MachineData → Prop}
    {E E' : (Int64 → Int64 → MachineData → Prop) × EStack⟨⟩}
    (h : ⦃P⦄ c ⪯[ofStateRepr MachineData.dmem] a ⦃Q; E⦄) (hE : ∀ x y t, E.1 x y t → E'.1 x y t) :
    ⦃P⦄ c ⪯[ofStateRepr MachineData.dmem] a ⦃Q; E'⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  refine PartialOrder.rel_trans (wrp_transport h.le_wrp Qa Ea) ?_
  refine WP.wp_monotone (x := c) PartialOrder.rel_refl ?_
  refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
  intro x t ht
  simp only [EPostsConcretization.ePosts_cons, Concretization.post_pi, ofStateRepr_pred] at ht ⊢
  obtain ⟨y, hxy, hb⟩ := ht
  exact ⟨y, hE _ _ _ hxy, hb⟩

end

end Ascent.Kraken
