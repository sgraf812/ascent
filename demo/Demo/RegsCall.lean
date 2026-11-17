import Demo.InstrCall
import Demo.Regs

/-!
# Calls with their registers lifted

`callRegs r k` is the call over the data memory alone, for the stack pointer `r` of the caller. It
pushes an unknown word `v` below `r` (`pushUnknownRegs`), runs the abstract callee `k v` with `v` as
its return address, and continues when `k` throws `v`. The call rule refines `callInstr kT` to
`callRegs r kL` from the refinement of `kT (r - 8) v` to `kL v` for every `v`, a premise that a
`Refinement` spec of the callee closes. The precondition `Pre` of that refinement names the
registers that the callee reads, and its exit relation `Ec` names the registers that the return
keeps. The caller continues with `Ec` alone, so the registers that the callee clobbers have no
value.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr ofStateRepr_pred)

namespace Distillery.Kraken

/-- Push an unknown 8-byte word below the stack pointer `r` and return it. -/
def pushUnknownRegs (r : BitVec 64) : BlockM DataMem Int64 :=
  ExceptT.mk fun m => do
    Demonic.assert ((Mem.loadInt m (r - 8#64) 8).isSome = true)
    let v ← (Demonic.unknown : Demonic Int64)
    pure (.ok v, m.storeInt (r - 8#64) 8 v.toBitVec.toInt)

theorem wp_pushUnknownRegs_fun (r : BitVec 64) (Q : Int64 → DataMem → Prop)
    (E : (Int64 → DataMem → Prop) × EStack⟨⟩) :
    wp (pushUnknownRegs r) Q E = fun m => (Mem.loadInt m (r - 8#64) 8).isSome = true ∧
      ∀ v, Q v (m.storeInt (r - 8#64) 8 v.toBitVec.toInt) :=
  funext fun _ => propext ⟨fun ⟨hm, h⟩ => ⟨hm, fun v => h v trivial⟩, fun ⟨hm, h⟩ => ⟨hm, fun v _ => h v⟩⟩

noncomputable def callRegs (r : BitVec 64) (k : Int64 → BlockM DataMem Unit) : BlockM DataMem Unit := do
  let v ← pushUnknownRegs r
  tryCatch (do k v; modifyIf (fun _ => False) id) fun l => modifyIf (fun _ => l = v) id

theorem ThrowsOnly.callRegs {P : Int64 → DataMem → Prop} (r : BitVec 64) (k : Int64 → BlockM DataMem Unit) :
    Distillery.ThrowsOnly P (callRegs r k) = True := eq_true fun Q E s hw => by
  simp only [Kraken.callRegs, WPMonadExact.wp_bind_eq, wp_pushUnknownRegs_fun, BlockLoop.wp_tryCatch,
    wp_modifyIf_fun] at hw ⊢
  exact hw

theorem tryCatch_callL_bind {β : Type} (r : BitVec 64) (k : Int64 → BlockM DataMem Unit)
    (f : Unit → BlockM DataMem β) (h : Int64 → BlockM DataMem β) :
    tryCatch (callRegs r k >>= f) h = callRegs r k >>= fun u => tryCatch (f u) h := by
  apply BlockLoop.ext_wp <;> intro Q E s hw <;>
    simp only [Kraken.callRegs, WPMonadExact.wp_bind_eq, wp_pushUnknownRegs_fun, BlockLoop.wp_tryCatch,
      wp_modifyIf_fun, wp_tryCatch_fun] at hw ⊢ <;>
    exact hw

section
variable {Q : Unit → Unit → MachineData → Prop} {E : (Int64 → Int64 → MachineData → Prop) × EStack⟨⟩}

theorem wrp_callA_callL {kT : BitVec 64 → Int64 → BlockM MachineData Unit}
    {kL : Int64 → BlockM DataMem Unit} {Pre : MachineData → Prop}
    {Qc : Unit → Unit → MachineData → Prop} {Ec : Int64 → Int64 → MachineData → Prop} {r : BitVec 64}
    (hk : ∀ v : Int64, ⦃Pre⦄ (kT (r - 8#64) v) ⪯[ofStateRepr MachineData.dmem] (kL v)
      ⦃Qc; (Ec, estack⟨⟩)⦄)
    (hex : ∀ c l t, Ec c l t → c = l ∧ t.regs.get64 .rsp = r) :
    (fun t => t.regs.get64 .rsp ≐ r ∧ (∀ v, Pre (t.push64 v)) ∧
      ∀ t', t'.regs.get64 .rsp ≐ r → ∀ c l, Ec c l t' → Q () () t')
      ⊑ wrp (ofStateRepr MachineData.dmem) (callInstr kT) (callRegs r kL) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at ht
  obtain ⟨⟨hr, hpre, hQ⟩, hw⟩ := ht
  have hr : t.regs.get64 .rsp = r := hr trivial
  simp only [callRegs, WPMonadExact.wp_bind_eq, wp_pushUnknownRegs_fun, BlockLoop.wp_tryCatch,
    wp_modifyIf_fun] at hw
  obtain ⟨hm, hw⟩ := hw
  simp only [callInstr, WPMonadExact.wp_bind_eq, wp_peek, wp_pushUnknown_fun, BlockLoop.wp_tryCatch,
    wp_modifyIf_fun]
  rw [hr]
  refine ⟨hm, fun v => ?_⟩
  let Qa' : Unit → DataMem → Prop := fun _ _ => False
  let Ea' : (Int64 → DataMem → Prop) × EStack⟨⟩ := (fun l m => l = v ∧ Qa () m, Ea.2)
  have hdm : (t.push64 v).dmem = t.dmem.storeInt (r - 8#64) 8 v.toBitVec.toInt := by
    simp only [MachineData.push64, hr]
  have hc := wrp_transport (hk v).le_wrp Qa' Ea' (t.push64 v)
    (by
      simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]
      refine ⟨hpre v, ?_⟩
      rw [hdm]
      refine WP.wp_monotone (x := kL v) ?_ ?_ _ (hw v)
      · intro u m hm'; exact hm'.1
      · exact Prod.mk_le _ _ _ (fun _ _ h => h) PartialOrder.rel_refl)
  refine WP.wp_monotone (x := kT (r - 8#64) v) ?_ ?_ _ hc
  · intro u t' ht'
    simp only [Concretization.post_pi, ofStateRepr_pred, Qa', and_false, exists_false] at ht'
  · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro c t' ht'
    simp only [Concretization.post_pi, ofStateRepr_pred] at ht'
    obtain ⟨l, hE, hlv, hqa⟩ := ht'
    obtain ⟨hcl, hrs⟩ := hex _ _ _ hE
    refine ⟨⟨hcl.trans hlv, hrs⟩, ?_⟩
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

end Distillery.Kraken
