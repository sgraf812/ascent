import Demo.L1Rel
import Demo.Lift

/-!
# Calls with their registers lifted

`callL r k` is the call over the data memory alone, for the stack pointer `r` of the caller. It
requires the cell below `r`, hides the return slot, runs the abstract callee `k` in the frame
`r - 8`, and returns when `k` throws. The call rule refines `callA kT` to `callL r kL` from the
refinement of `kT (r - 8)` to `kL`, a premise that a `Refinement` spec of the callee closes. The
precondition `Pre` of that refinement names the registers that the callee reads, and its exit
relation `Ec` names the registers that the return keeps. The caller continues with `Ec` alone, so
the registers that the callee clobbers have no value.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Kraken

noncomputable def callL (r : BitVec 64) (k : BlockM DataMem Unit) : BlockM DataMem Unit := do
  modifyIf (fun m => (Mem.loadInt m (r - 8#64) 8).isSome = true) (hideSlot (r - 8#64))
  tryCatch (do k; modifyIf (fun _ => False) id) fun _ => pure ()

theorem ThrowsOnly.callL {P : Int64 → DataMem → Prop} (r : BitVec 64) (k : BlockM DataMem Unit) :
    Ascent.ThrowsOnly P (callL r k) = True := eq_true fun Q E s hw => by
  simp only [Kraken.callL, WPMonadExact.wp_bind_eq, wp_modifyIf, BlockLoop.wp_tryCatch, wp_modifyIf_fun,
    WPMonadExact.wp_pure_eq] at hw ⊢
  exact hw

theorem tryCatch_callL_bind {β : Type} (r : BitVec 64) (k : BlockM DataMem Unit)
    (f : Unit → BlockM DataMem β) (h : Int64 → BlockM DataMem β) :
    tryCatch (callL r k >>= f) h = callL r k >>= fun u => tryCatch (f u) h := by
  apply BlockLoop.ext_wp <;> intro Q E s hw <;>
    simp only [Kraken.callL, WPMonadExact.wp_bind_eq, wp_modifyIf, BlockLoop.wp_tryCatch,
      wp_modifyIf_fun, wp_tryCatch_fun, WPMonadExact.wp_pure_eq] at hw ⊢ <;>
    exact hw

section
variable {Q : Unit → Unit → MachineData → Prop} {E : (Int64 → Int64 → MachineData → Prop) × EStack⟨⟩}

theorem wrp_callA_callL {kT : BitVec 64 → BlockM MachineData Unit} {kL : BlockM DataMem Unit}
    {Pre : MachineData → Prop} {Ec : Int64 → Int64 → MachineData → Prop} {r : BitVec 64}
    (hk : ⦃Pre⦄ (kT (r - 8#64)) ⪯[ofStateRepr MachineData.dmem] kL
      ⦃fun _ _ _ => False; (Ec, estack⟨⟩)⦄)
    (hrsp : ∀ l l' t, Ec l l' t → t.regs.get64 .rsp = r) :
    (fun t => t.regs.get64 .rsp ≐ r ∧ Pre (hidePush r t) ∧
      ∀ t', t'.regs.get64 .rsp ≐ r → ∀ l l', Ec l l' t' → Q () () t')
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
  have hc := wrp_transport hk.le_wrp Qa' Ea' (hidePush r t)
    (by
      simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, hidePush_dmem]
      refine ⟨hpre, ?_⟩
      refine WP.wp_monotone (x := kL) ?_ ?_ _ hw
      · intro u m hm'; exact hm'.1
      · exact Prod.mk_le _ _ _ (fun _ _ h => h) PartialOrder.rel_refl)
  refine WP.wp_monotone (x := kT (r - 8#64)) ?_ ?_ _ hc
  · intro u t' ht'
    simp only [Concretization.post_pi, ofStateRepr_pred, Qa', and_false, exists_false] at ht'
  · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l t' ht'
    simp only [Concretization.post_pi, ofStateRepr_pred] at ht'
    obtain ⟨l', hE, hqa⟩ := ht'
    have hrs := hrsp _ _ _ hE
    show t'.regs.get64 .rsp = r ∧ (ofStateRepr MachineData.dmem).post Q Qa () t'
    refine ⟨hrs, ?_⟩
    rw [Concretization.post_pi]
    exact ⟨(), hQ t' (PureRefinement.of_rel hrs) _ _ hE, hqa⟩

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
