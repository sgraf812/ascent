import Demo.Lift

/-!
# `zipWithAdd` with its registers lifted

`zipWithAddL` is `zipWithAddT` over the data memory alone. The registers the loop only reads are
parameters, `rax` is a `let mut` of the loop, and `r8` is a pair of bound values. The memory steps
keep the guards of the first layer: a load needs a mapped cell, a store also needs the cell apart
from the return slot at `rsp`, and the return needs a mapped return slot.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr

namespace Ascent.Kraken

/-! ## The lifted program -/

noncomputable def zipWithAddL (rdi rsi rdx rcx rsp : BitVec 64) : BlockM DataMem Unit := do
  if CondCode.cmp .le (rcx &&& rcx) 0 then retAt rsp
  else
    let mut rax : BitVec 64 := 0
    repeat'
      let x ← load8 (rsi + rax * 8)
      let y ← load8 (rdi + rax * 8)
      store8 rsp (rdx + rax * 8) (y + x)
      rax := rax + 1
      if CondCode.cmp .nz rcx rax then continue
      else
        retAt rsp
        break

/-! ## Lockstep loops

`wp_fixLoop_lockstep`: a concrete loop over the machine state refines an abstract loop over the
memory when one abstract iteration simulates one concrete iteration under the relation `R` between
the machine state and the abstract loop value. The proof is fixpoint induction over the abstract
loop. -/

section
variable {βa : Type} (R : MachineData → βa → Prop)
  (fa : Unit → βa → BlockM DataMem (ForInStep βa)) (fc : Unit → PUnit → BlockM MachineData (ForInStep PUnit))
  (Qa : βa → DataMem → Prop) (Qc : PUnit → MachineData → Prop)
  (Ea : (CfgLabel → DataMem → Prop) × EStack⟨⟩) (Ec : (CfgLabel → MachineData → Prop) × EStack⟨⟩)

theorem wp_fixLoop_lockstep
    (hbody : ∀ ab t, R t ab → ∀ (Ka : βa → DataMem → Prop) (Kc : MachineData → Prop),
      (∀ ab' t', R t' ab' → Ka ab' t'.dmem → Kc t') → (∀ v t', R t' v → Qa v t'.dmem → Qc () t') →
      wp (fa () ab) (fun r m => match r with | .done v => Qa v m | .yield v => Ka v m) Ea t.dmem →
      wp (fc () PUnit.unit) (fun r t' => match r with | .done _ => Qc () t' | .yield _ => Kc t') Ec t)
    (hQ : ∀ v t', R t' v → Qa v t'.dmem → Qc () t')
    (ab : βa) (t : MachineData) (hR : R t ab)
    (h : wp (FixLoop.mk.forIn ab fa) Qa Ea t.dmem) : wp (FixLoop.mk.forIn PUnit.unit fc) Qc Ec t := by
  haveI : Nonempty βa := ⟨ab⟩
  have := FixLoop.forIn_induct fa
    (fun g => ∀ ab t, R t ab → wp (g ab) Qa Ea t.dmem → wp (FixLoop.mk.forIn PUnit.unit fc) Qc Ec t)
    (admissible_pi _ fun ab => admissible_pi _ fun t => admissible_pi _ fun _ =>
      admissible_apply (fun _ u => wp u Qa Ea t.dmem → wp (FixLoop.mk.forIn PUnit.unit fc) Qc Ec t) ab
        (admissible_wp_imp _ Ea t.dmem _)) ?_
  · exact this ab t hR h
  intro g ih ab t hR hw
  rw [FixLoop.forIn_eq, WPMonadExact.wp_bind_eq]
  simp only [FixLoop.step, WPMonadExact.wp_bind_eq] at hw
  refine WP.wp_monotone_post (x := fc () PUnit.unit) ?_ t
    (hbody ab t hR (fun v m => wp (g v) Qa Ea m) (fun t' => wp (FixLoop.mk.forIn PUnit.unit fc) Qc Ec t')
      (fun ab' t' hR' hK => ih ab' t' hR' hK) hQ ?_)
  · intro r t' hr
    cases r <;> simp only [WPMonadExact.wp_pure_eq] at hr ⊢ <;> exact hr
  · refine WP.wp_monotone_post (x := fa () ab) ?_ t.dmem hw
    intro r m hr
    cases r <;> simp only [WPMonadExact.wp_pure_eq] at hr ⊢ <;> exact hr

end

/-- The relation of one iteration of two lockstep loops: both continue, or both stop, with the loop
values related by `R`. -/
def StepRel {βa : Type} (R : MachineData → βa → Prop) : ForInStep PUnit → ForInStep βa → MachineData → Prop
  | .done _, .done v, t => R t v
  | .yield _, .yield v, t => R t v
  | _, _, _ => False

/-- `wp_fixLoop_lockstep` as a refinement: a concrete loop over the machine state refines an
abstract loop over the memory when each iteration refines with `StepRel R`. -/
theorem refines_fixLoop_lockstep {βa : Type} (R : MachineData → βa → Prop)
    {fa : Unit → βa → BlockM DataMem (ForInStep βa)}
    {fc : Unit → PUnit → BlockM MachineData (ForInStep PUnit)}
    {E : (CfgLabel → CfgLabel → MachineData → Prop) × EStack⟨⟩}
    (hbody : ∀ ab, ⦃(R · ab)⦄ (fc () PUnit.unit) ⪯[Concretization.ofStateRepr MachineData.dmem]
      (fa () ab) ⦃StepRel R; E⦄) (ab : βa) :
    ⦃(R · ab)⦄ (FixLoop.mk.forIn PUnit.unit fc) ⪯[Concretization.ofStateRepr MachineData.dmem]
      (FixLoop.mk.forIn ab fa) ⦃fun _ v t => R t v; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred] at ht
  refine wp_fixLoop_lockstep R fa fc Qa _ Ea _ ?_ ?_ ab t ht.1 ht.2
  · intro ab t' hR Ka Kc hK hQ hw
    have hb := wrp_transport (hbody ab).le_wrp
      (fun r m => match r with | .done v => Qa v m | .yield v => Ka v m) Ea t'
      (by simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]; exact ⟨hR, hw⟩)
    refine WP.wp_monotone_post (x := fc () PUnit.unit) ?_ t' hb
    intro rc t'' h''
    rw [Concretization.post_pi] at h''
    obtain ⟨ra, hrel, hq⟩ := h''
    simp only [Concretization.ofStateRepr_pred] at hq
    cases rc <;> cases ra <;> simp only [StepRel] at hrel
    · exact hQ _ t'' hrel hq
    · exact hK _ t'' hrel hq
  · intro v t' hR hq
    rw [Concretization.post_pi]
    exact ⟨v, hR, hq⟩

/-! ## `zipWithAddT` refines to `zipWithAddL` -/

/-- The registers that `zipWithAddL` takes as parameters, and `rax` as its loop value. -/
def LiftRel (rdi rsi rdx rcx rsp : BitVec 64) (t : MachineData) (rax : BitVec 64) : Prop :=
  t.regs.get64 .rdi = rdi ∧ t.regs.get64 .rsi = rsi ∧ t.regs.get64 .rdx = rdx
    ∧ t.regs.get64 .rcx = rcx ∧ t.regs.get64 .rsp = rsp ∧ t.regs.get64 .rax = rax

theorem wp_ret_of_retAt {rsp : BitVec 64} {Ea : (CfgLabel → DataMem → Prop) × EStack⟨⟩}
    {Qu : Unit → DataMem → Prop} {Qc : Unit → MachineData → Prop} {t : MachineData}
    (hrsp : t.regs.get64 .rsp = rsp) (h : wp (retAt rsp) Qu Ea t.dmem) :
    wp (exitIf retOk ret .exit) Qc (fun l t' => Ea.1 l t'.dmem ∧ t'.regs.get64 .rsp = rsp + 8, Ea.2) t := by
  rw [wp_retAt] at h
  rw [wp_exitIf, retOk, ret]
  refine ⟨by rw [hrsp]; exact h.1, h.2, ?_⟩
  rw [Reg64s.get64_set64]
  simp [hrsp]

section
variable [Host] [FunDecls] [Embeds zipWithAdd]

theorem wp_zipWithAddT_of_L (s : MachineData) (ra : Int64) {rdi rsi rdx rcx rsp : BitVec 64}
    (Qa : Unit → DataMem → Prop) (Ea : (CfgLabel → DataMem → Prop) × EStack⟨⟩) (t : MachineData)
    (hargs : LiftRel rdi rsi rdx rcx rsp t (t.regs.get64 .rax))
    (h : wp (zipWithAddL rdi rsi rdx rcx rsp) Qa Ea t.dmem) :
    wp (zipWithAddT s ra) (fun u t' => Qa u t'.dmem)
      (fun l t' => Ea.1 l t'.dmem ∧ t'.regs.get64 .rsp = rsp + 8, Ea.2) t := by
  obtain ⟨hrdi, hrsi, hrdx, hrcx, hrsp, -⟩ := hargs
  unfold zipWithAddT zipWithAddL at *
  have hrcx' : t.regs.rcx.toBitVec = rcx := hrcx
  rw [wp_condState, hrcx']
  cases hc : CondCode.cmp .le (rcx &&& rcx) 0
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [WPMonadExact.wp_bind_eq] at h
    rw [WPMonadExact.wp_bind_eq, wp_modifyIf, xorReg32Reg32]
    refine ⟨trivial, ?_⟩
    refine wp_fixLoop_lockstep (fun t' rax => LiftRel rdi rsi rdx rcx rsp t' rax) _ _ _ _ _ _ ?_
      (fun _ _ _ hq => by simpa only [WPMonadExact.wp_pure_eq] using hq) 0 _ ?_ h
    · intro ab t' hR Ka Kc hK _ hw
      obtain ⟨hrdi', hrsi', hrdx', hrcx', hrsp', hrax'⟩ := hR
      have hoff : BitVec.ofInt 64 (Int64.toInt 0) = 0 := rfl
      have hz : ∀ x : BitVec 64, x + 0 = x := fun x => BitVec.add_zero x
      have ercx : ∀ r : Reg64s, r.rcx.toBitVec = r.get64 .rcx := fun _ => rfl
      have erax : ∀ r : Reg64s, r.rax.toBitVec = r.get64 .rax := fun _ => rfl
      simp only [WPMonadExact.wp_bind_eq, wp_load8, wp_store8] at hw
      simp only [WPMonadExact.wp_bind_eq, movRegSib8, addRegSib8, movSib8Reg, incReg, wp_modifyIf,
        loadOk8, storeOk8, sib8, wp_condState, ercx, erax, Reg64s.get64_set64, reduceCtorEq,
        ↓reduceIte, hrdi', hrsi', hrdx', hrcx', hrsp', hrax', hoff, hz, true_and]
      obtain ⟨hB, hA, hO, hw'⟩ := hw
      refine ⟨hB, hA, hO, ?_⟩
      have hR' : ∀ v₈ v (m : DataMem), LiftRel rdi rsi rdx rcx rsp
          { t' with regs := ((t'.regs.set64 .r8 v₈).set64 .r8 v).set64 .rax (ab + 1), dmem := m }
            (ab + 1) := by
        intro v₈ v m
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrdi', hrsi', hrdx', hrcx', hrsp']
      cases hn : CondCode.cmp .nz rcx (ab + 1)
      · simp only [hn, Bool.false_eq_true, ↓reduceIte, wp_toDone, WPMonadExact.wp_bind_eq] at hw' ⊢
        exact wp_ret_of_retAt (hR' _ _ _).2.2.2.2.1 hw'
      · simp only [hn, ↓reduceIte, WPMonadExact.wp_pure_eq] at hw' ⊢
        exact hK (ab + 1) _ (hR' _ _ _) hw'
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrdi, hrsi, hrdx, hrcx, hrsp]
      simp
  · simp only [hc, ↓reduceIte] at h ⊢
    exact wp_ret_of_retAt hrsp h

theorem zipWithAddT_refines_L (s : MachineData) (ra : Int64) (rdi rsi rdx rcx rsp : BitVec 64) :
    ⦃(fun t => LiftRel rdi rsi rdx rcx rsp t (t.regs.get64 .rax))⦄ (zipWithAddT s ra)
      ⪯[Concretization.ofStateRepr MachineData.dmem] (zipWithAddL rdi rsi rdx rcx rsp)
      ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = rsp + 8, estack⟨⟩)⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred] at ht
  refine WP.wp_monotone (x := zipWithAddT s ra) ?_ ?_ t (wp_zipWithAddT_of_L s ra Qa Ea t ht.1 ht.2)
  · intro u t' hq
    rw [Concretization.post_pi]
    exact ⟨u, trivial, hq⟩
  · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l t' ⟨hq, hrsp⟩
    simp only [EPostsConcretization.ePosts_cons]
    rw [Concretization.post_pi]
    exact ⟨l, ⟨rfl, hrsp⟩, hq⟩

end

end Ascent.Kraken
