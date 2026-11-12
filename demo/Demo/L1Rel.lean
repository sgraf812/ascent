import Demo.L1Gen

/-!
# Calls

`JRel (Mem.SubSlots P)` hides the return slots `P` from the abstract state: the abstract memory
lacks their cells, and the concrete memory holds the return addresses there. The return reads its
address from the concrete slot, so the abstract program of a function does not depend on its
return address. A call refines `callA k`, one run of the abstract callee `k` with its return slot
hidden, for every return address that the call pushes.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRel ofStateRepr_pred ofStateRel_pred)
open scoped Program.WP

namespace Ascent.Kraken

/-! ## The return under hidden return slots

The return slot of the frame `r₀` is a cell of `P`: the abstract state lacks it, and the concrete
state holds the return address `ra` there. The abstract return assumes that the stack pointer is
`r₀` and throws `L`; the concrete return reads `ra` from its slot. -/

section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}

theorem stayIn_ret (r₀ : BitVec 64) (s : MachineData) :
    stayIn r₀ { s with regs := s.regs.set64 .rsp (r₀ + 8#64) } = false := by
  simp only [stayIn, stayAt, Reg64s.get64_set64, ↓reduceIte]
  rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rfl

@[ascend] theorem wrp_ret_slots {P : DataMem} {p : Program} {r₀ : BitVec 64} {ra L : Int64}
    (hP : (P.loadInt r₀ 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some ra) (asz osz : Width) :
    (fun _ => True)
      ⊑ wrp (ofStateRel (JRel (Mem.SubSlots P))) (Directive.instr (.regular asz osz .ret))
        (exitIf (fun st => st.regs.get64 .rsp = r₀) (setReg64 .rsp fun _ => r₀ + 8#64) L)
        Q (BlockExit p r₀ (RetExit r₀ ra L)) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, wp_exitIf] at hs
  obtain ⟨-, a, hJ, hr, hE⟩ := hs
  have hrs : s.regs.get64 .rsp = r₀ := by rw [← JRel.regs hJ]; exact hr
  have hsub : Mem.Sub P s.dmem := fun q v hq => (hJ.2.2.2.2 q v hq).1
  have ha : s.retAddr = some ra := by
    rw [MachineData.retAddr_eq, hrs]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
      (show (P.loadInt r₀ 8).isSome = true by rw [← Option.isSome_map, hP]; rfl)
    rw [hsub.loadInt hx]
    rw [hx] at hP
    exact hP
  refine (Program.WP.Spec.ret asz osz).le_wp s ⟨by rw [ha]; rfl, ?_⟩
  show (ofStateRel (JRel (Mem.SubSlots P))).post (BlockExit p r₀ (RetExit r₀ ra L)) Ea.1 _ _
  simp only [Concretization.post_pi, ofStateRel_pred]
  refine ⟨L, Or.inr ⟨?_, by rw [ha]; rfl⟩, _, ?_, hE⟩
  · rw [hrs]; exact stayIn_ret r₀ s
  · refine ⟨?_, hJ.2.1, hJ.2.2.1, hJ.2.2.2⟩
    simp only [setReg64_regs, abs_regs, JRel.regs hJ, hrs]

@[ascend default + 1] theorem wrp_ret_slots_cons {P : DataMem} {p : Program} {r₀ : BitVec 64} {ra L : Int64}
    (hP : (P.loadInt r₀ 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some ra) (asz osz : Width)
    (q : Program) (hN : Program.labels (Directive.instr (.regular asz osz .ret) :: q) = []) :
    (fun _ => True)
      ⊑ wrp (ofStateRel (JRel (Mem.SubSlots P))) (Directive.instr (.regular asz osz .ret) :: q)
        (exitIf (fun st => st.regs.get64 .rsp = r₀) (setReg64 .rsp fun _ => r₀ + 8#64) L)
        Q (BlockExit p r₀ (RetExit r₀ ra L)) := by
  rw [← exitIf_bind _ _ _ (fun _ => pure ())]
  exact PartialOrder.rel_trans (wrp_ret_slots hP asz osz) (wrp_cons _ q _ (fun _ => pure ()) hN)

end

/-! ## Calls under hidden return slots

`callA k` calls the abstract function `k`: it requires the cell below the stack pointer `r`, pushes
the frame `r - 8`, hides the return slot, runs `k (r - 8)`, and returns when `k` leaves with the
stack pointer `r`. The callee's exception is the return, whatever its label; falling through the end
of the callee is undefined behaviour. -/

/-- The state at the entry of a callee at the frame `r - 8`, with its return slot hidden. -/
def hidePush (r : BitVec 64) (s : MachineData) : MachineData :=
  { s with regs := s.regs.set64 .rsp (r - 8#64),
           dmem := s.dmem.filter fun p _ => !decide (Mem.Blocks.Inside p 1 [(r - 8#64, 8)]) }

noncomputable def callA (k : BitVec 64 → BlockM MachineData Unit) : BlockM MachineData Unit := do
  let r ← peek fun s => s.regs.get64 .rsp
  modifyIf (fun s => (Mem.loadInt s.dmem (r - 8#64) 8).isSome = true) (hidePush r)
  tryCatch (do k (r - 8#64); modifyIf (fun _ => False) id) fun _ =>
    modifyIf (fun s => s.regs.get64 .rsp = r) id

theorem wp_modifyIf_fun {σ : Type} (g : σ → Prop) (f : σ → σ) (Q : Unit → σ → Prop)
    (E : (Int64 → σ → Prop) × EStack⟨⟩) : wp (modifyIf g f) Q E = fun s => g s ∧ Q () (f s) :=
  funext fun s => wp_modifyIf Q E s g f

theorem wp_tryCatch_fun {σ α : Type} (x : BlockM σ α) (h : Int64 → BlockM σ α) (Q : α → σ → Prop)
    (E : (Int64 → σ → Prop) × EStack⟨⟩) : wp (tryCatch x h) Q E = wp x Q (fun l => wp (h l) Q E, E.2) :=
  funext fun s => BlockLoop.wp_tryCatch x h Q E s

theorem ThrowsOnly.callA {P : Int64 → MachineData → Prop} (k : BitVec 64 → BlockM MachineData Unit) :
    Ascent.ThrowsOnly P (callA k) = True := eq_true fun Q E s hw => by
  simp only [Kraken.callA, WPMonadExact.wp_bind_eq, wp_peek, wp_modifyIf, BlockLoop.wp_tryCatch,
    wp_modifyIf_fun] at hw ⊢
  exact hw

theorem tryCatch_callA_bind {β : Type} (k : BitVec 64 → BlockM MachineData Unit)
    (f : Unit → BlockM MachineData β) (h : Int64 → BlockM MachineData β) :
    tryCatch (callA k >>= f) h = callA k >>= fun u => tryCatch (f u) h := by
  apply BlockLoop.ext_wp <;> intro Q E s hw <;>
    simp only [Kraken.callA, WPMonadExact.wp_bind_eq, wp_peek, wp_modifyIf, BlockLoop.wp_tryCatch,
      wp_modifyIf_fun, wp_tryCatch_fun] at hw ⊢ <;>
    exact hw

theorem jrel_hidePush {P : DataMem} {s a : MachineData} (h : JRel (Mem.SubSlots P) s a) (ra : Int64)
    (hm : (Mem.loadInt a.dmem (a.regs.get64 .rsp - 8#64) 8).isSome = true) :
    JRel (Mem.SubSlots (P.storeInt (s.regs.get64 .rsp - 8#64) 8 ra.toBitVec.toInt)) (s.push64 ra)
      (hidePush (a.regs.get64 .rsp) a) := by
  have hr : a.regs = s.regs := JRel.regs h
  refine ⟨?_, h.2.1, h.2.2.1, ?_, ?_⟩
  · simp only [hidePush, MachineData.push64, abs_regs, hr]
  · intro q v hq
    simp only [hidePush, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_filter'] at hq
    cases hqa : a.dmem[q]? with
    | none => rw [hqa] at hq; exact nomatch hq
    | some y =>
      rw [hqa] at hq
      simp only [Option.filter] at hq
      split at hq
      · rename_i hin
        cases hq
        have hs := h.2.2.2.1 q v (by rw [Std.ExtHashMap.get?_eq_getElem?]; exact hqa)
        simp only [abs_dmem, MachineData.push64] at hs ⊢
        rw [Mem.get?_storeInt]
        have hn : ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp - 8#64))[q]? = none := by
          apply Std.ExtHashMap.getElem?_eq_none
          intro hmem
          obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hmem
          rw [Int.toBytes_length] at hi
          rw [hr] at hin
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hin
          exact hin ((Mem.Blocks.Inside.base (Nat.le_refl 8)).add_ofNat hi)
        rw [hn]
        exact hs
      · exact nomatch hq
  · intro q v hq
    have hr' : a.regs.get64 .rsp = s.regs.get64 .rsp := by rw [hr]
    simp only [abs_dmem, MachineData.push64, hidePush]
    rw [Mem.get?_storeInt] at hq ⊢
    cases hat : ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp - 8#64))[q]? with
    | some y =>
      rw [hat] at hq
      refine ⟨hq, ?_⟩
      have hmem : q ∈ (Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp - 8#64) :=
        Std.ExtHashMap.isSome_getElem?_iff_mem.mp (by rw [hat]; rfl)
      obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hmem
      rw [Int.toBytes_length] at hi
      have hin : Mem.Blocks.Inside (s.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 i) 1
          [(a.regs.get64 .rsp - 8#64, 8)] := by
        rw [hr']; exact (Mem.Blocks.Inside.base (Nat.le_refl 8)).add_ofNat hi
      simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_filter']
      cases a.dmem[s.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 i]? with
      | none => rfl
      | some z => simp only [Option.filter, decide_eq_true hin, Bool.not_true]; rfl
    | none =>
      rw [hat] at hq
      simp only [Option.none_or] at hq
      obtain ⟨h1, h2⟩ := h.2.2.2.2 q v hq
      simp only [abs_dmem] at h1
      refine ⟨by simpa using h1, ?_⟩
      simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_filter']
      rw [Std.ExtHashMap.get?_eq_getElem?] at h2
      rw [h2]
      rfl


theorem subSlots_of_storeInt {P m m' : DataMem} {q : BitVec 64} {x : Int}
    (h : Mem.SubSlots (P.storeInt q 8 x) m m') (hq : ∀ i < 8, P.get? (q + BitVec.ofNat 64 i) = none) :
    Mem.SubSlots P m m' := by
  refine ⟨h.1, fun p v hp => ?_⟩
  have hn : ((Int.toBytes 8 x).At q)[p]? = none := by
    apply Std.ExtHashMap.getElem?_eq_none
    intro hmem
    obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hmem
    rw [Int.toBytes_length] at hi
    rw [hq i hi] at hp
    exact nomatch hp
  exact h.2 p v (by rw [Mem.get?_storeInt, hn]; exact hp)

section
variable [Host] [FunDecls]

/-- A call refines `callA` of the abstract callee `k`, given a refinement of the callee's body for
every set of hidden slots `P'`, every frame `r₀` and every return address `ra` in its slot. -/
@[ascend] theorem wrp_call_slots {P : DataMem} {f : Label} {g : Fragment} (hg : FunDecls.at (label f) = some g)
    (asz osz : Width) (L : Int64) {k : BitVec 64 → Int64 → BlockM MachineData Unit}
    (hk : ∀ (P' : DataMem) (r₀ : BitVec 64) (ra : Int64),
      (P'.loadInt r₀ 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some ra →
      ⦃fun s => s.regs.get64 .rsp = r₀⦄ g.prog ⪯[ofStateRel (JRel (Mem.SubSlots P'))] (k r₀ L)
        ⦃fun _ _ => ⊤; RetExit r₀ ra L⦄)
    {Q : Unit → Unit → MachineData → Prop} {E : Int64 → Int64 → MachineData → Prop} :
    (fun _ => ∀ t, Q () () t)
      ⊑ wrp (ofStateRel (JRel (Mem.SubSlots P)))
          (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
          (callA fun r => k r L) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred] at hs
  obtain ⟨hQ, a, hJ, hw⟩ := hs
  simp only [callA, WPMonadExact.wp_bind_eq, wp_peek, wp_modifyIf, BlockLoop.wp_tryCatch,
    wp_modifyIf_fun] at hw
  obtain ⟨hm, hw⟩ := hw
  have hr : a.regs = s.regs := JRel.regs hJ
  have hrsp : a.regs.get64 .rsp = s.regs.get64 .rsp := by rw [hr]
  refine (Program.WP.wp_call_iff hg).mpr fun [h : Embeds _] => ?_
  let ra := h.embedding.endAddr
  refine ⟨?_, ?_⟩
  · have := hJ.2.2.2.1.loadInt_isSome hm
    rwa [hrsp, abs_dmem] at this
  rw [FunDecls.body_eq hg]
  let P' := P.storeInt (s.regs.get64 .rsp - 8#64) 8 ra.toBitVec.toInt
  have hP' : (P'.loadInt (s.regs.get64 .rsp - 8#64) 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i))
      = some ra := by
    simp only [P', Mem.loadInt_storeInt_64, Option.map_some, Int64.ofBitVec_ofBytes_toBytes]
  have hslot : ∀ i < 8, P.get? (s.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 i) = none := fun i hi => by
    cases hp : P.get? (s.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 i) with
    | none => rfl
    | some v =>
      have h2 := (hJ.2.2.2.2 _ v hp).2
      have h3 := Mem.get?_isSome_of_loadInt hm hi
      rw [hrsp, h2] at h3
      exact nomatch h3
  let Qa' : Unit → MachineData → Prop := fun _ _ => False
  let Ea' : (Int64 → MachineData → Prop) × EStack⟨⟩ :=
    (fun _ b => b.regs.get64 .rsp = s.regs.get64 .rsp ∧ Qa () b, estack⟨⟩)
  have hwk : wp (k (s.regs.get64 .rsp - 8#64) L) Qa' Ea' (hidePush (a.regs.get64 .rsp) a) := by
    rw [← hrsp]
    refine WP.wp_monotone (x := k (a.regs.get64 .rsp - 8#64) L) ?_ ?_ _ hw
    · intro u t ht
      exact ht.1
    · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l t ht
      exact ⟨by rw [hrsp] at ht; exact ht.1, ht.2⟩
  have hc := wrp_transport (hk P' (s.regs.get64 .rsp - 8#64) ra hP').le_wrp Qa' Ea' (s.push64 ra)
    (by
      simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
      refine ⟨?_, _, jrel_hidePush hJ ra hm, hwk⟩
      simp only [MachineData.regs_push64, Reg64s.get64_set64, ↓reduceIte])
  refine Program.wp_mono (fun u hu => ?_) (fun u hu => ?_) hc
  · simp only [Concretization.post_pi, ofStateRel_pred, Qa', and_false, exists_false] at hu
  · simp only [ePosts_ret, Concretization.post_pi, ofStateRel_pred, RetExit_eq] at hu
    obtain ⟨l, ⟨-, hpc⟩, b, hJb, hrb, hqa⟩ := hu
    rw [if_pos hpc]
    simp only [Concretization.post_pi, ofStateRel_pred]
    exact ⟨(), hQ _, b, ⟨hJb.1, hJb.2.1, hJb.2.2.1, subSlots_of_storeInt hJb.2.2.2 hslot⟩, hqa⟩

end

end Ascent.Kraken
