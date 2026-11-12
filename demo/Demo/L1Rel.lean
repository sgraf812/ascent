import Demo.L1Gen

/-!
# Calls

A call refines `withRa k` under `JRel Mem.Sub`, the relation whose abstract states forget memory.
The call pushes a different return address for each `ra`, and `withRa` erases the return slot from
the abstract state, so one abstract outcome serves every `ra`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRel ofStateRepr_pred ofStateRel_pred)
open scoped Program.WP

namespace Ascent.Kraken

theorem jsub_push64 {s a : MachineData} (h : JRel Mem.Sub s a) (ra : Int64) : JRel Mem.Sub (s.push64 ra) (a.push64 ra) := by
  obtain ⟨hr, hz, hs, hm⟩ := h
  refine ⟨?_, hz, hs, ?_⟩
  · simp only [MachineData.push64, abs_regs] at hr ⊢
    rw [hr]
  · simp only [MachineData.push64, abs_dmem, abs_regs] at hm hr ⊢
    rw [hr]
    exact hm.storeInt _ _ _

/-! ## Calls

`withRa k` runs `k r ra` from the state with the return address `ra` pushed at `r = rsp - 8`, for
every `ra`. An exit to `ra` is the return, and the return slot is erased from the state. If every
`ra` gives the same outcome, `withRa k` has that outcome; otherwise it is undefined behaviour. -/

/-- The memory without the return slot below `r`. -/
def eraseSlot (r : BitVec 64) (t : MachineData) : MachineData :=
  { t with dmem := t.dmem.filter fun p _ => !decide (Mem.Blocks.Inside p 1 [(r - 8#64, 8)]) }

theorem Mem.Sub.erase_left {m m' : DataMem} (h : Mem.Sub m m') (r : BitVec 64) :
    Mem.Sub (m.filter fun p _ => !decide (Mem.Blocks.Inside p 1 [(r - 8#64, 8)])) m' := fun p x hp => by
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_filter'] at hp
  apply h p x
  rw [Std.ExtHashMap.get?_eq_getElem?]
  cases hm : m[p]? with
  | none => rw [hm] at hp; exact absurd hp (by simp)
  | some y => rw [hm] at hp; simp only [Option.filter] at hp; split at hp <;> simp_all

theorem jsub_eraseSlot {t b : MachineData} (h : JRel Mem.Sub t b) (r : BitVec 64) : JRel Mem.Sub t (eraseSlot r b) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.erase_left r⟩

/-- The outcome of a call for the return address `ra`, as the caller sees it. -/
noncomputable def callOutcome (k : BitVec 64 → Int64 → BlockM MachineData Unit) (s : MachineData)
    (ra : Int64) : UB (Except Int64 Unit × MachineData) :=
  ((k (s.regs.get64 .rsp - 8#64) ra).run.run (s.push64 ra)).bind fun
    | (.ok (), _) => none
    | (.error a, t) => some (if a = ra then .ok () else .error a, eraseSlot (s.regs.get64 .rsp) t)

open Classical in
noncomputable def withRaRun (k : BitVec 64 → Int64 → BlockM MachineData Unit) (s : MachineData) :
    UB (Except Int64 Unit × MachineData) :=
  if (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome then
    if h : ∃ o, ∀ ra, callOutcome k s ra = o then Classical.choose h else UB.fail
  else UB.fail

/-- The call of the abstract function `k`: undefined behaviour unless the return slot is mapped and
every return address gives the same outcome. -/
noncomputable def withRa (k : BitVec 64 → Int64 → BlockM MachineData Unit) : BlockM MachineData Unit :=
  ExceptT.mk fun s => withRaRun k s

theorem withRa_run (k : BitVec 64 → Int64 → BlockM MachineData Unit) (s : MachineData) :
    (withRa k).run.run s = withRaRun k s := rfl

theorem withRa_some {k : BitVec 64 → Int64 → BlockM MachineData Unit} {s : MachineData}
    {r : Except Int64 Unit × MachineData} (h : withRaRun k s = some r) :
    (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true ∧ ∀ ra, callOutcome k s ra = some r := by
  unfold withRaRun at h
  by_cases hm : (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true
  · rw [if_pos hm] at h
    by_cases hex : ∃ o, ∀ ra, callOutcome k s ra = o
    · rw [dif_pos hex] at h
      refine ⟨hm, fun ra => ?_⟩
      rw [Classical.choose_spec hex ra, h]
    · rw [dif_neg hex] at h
      exact nomatch (h : (none : Option _) = some r)
  · rw [if_neg hm] at h
    exact nomatch (h : (none : Option _) = some r)

theorem withRa_eq_of {k : BitVec 64 → Int64 → BlockM MachineData Unit} {s : MachineData}
    {o : UB (Except Int64 Unit × MachineData)}
    (hm : (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true)
    (h : ∀ ra, callOutcome k s ra = o) : withRaRun k s = o := by
  have hex : ∃ o, ∀ ra, callOutcome k s ra = o := ⟨o, h⟩
  unfold withRaRun
  rw [if_pos hm, dif_pos hex, ← Classical.choose_spec hex 0, h]

theorem callOutcome_of_run {k : BitVec 64 → Int64 → BlockM MachineData Unit} {s : MachineData} {ra : Int64}
    {r : Except Int64 Unit × MachineData} (h : callOutcome k s ra = some r) :
    ∃ a b, (k (s.regs.get64 .rsp - 8#64) ra).run.run (s.push64 ra) = some (.error a, b) ∧
      r = (if a = ra then .ok () else .error a, eraseSlot (s.regs.get64 .rsp) b) := by
  unfold callOutcome at h
  cases hr : (k (s.regs.get64 .rsp - 8#64) ra).run.run (s.push64 ra) with
  | none => rw [hr] at h; exact nomatch h
  | some p =>
    rw [hr] at h
    obtain ⟨e, b⟩ := p
    cases e with
    | ok u => exact nomatch h
    | error a =>
      simp only [Option.bind_some] at h
      exact ⟨a, b, rfl, (Option.some.inj h).symm⟩

section
variable [Host] [FunDecls]

/-- A call refines `withRa k` when the body of the callee refines `k r₀ ra` for every frame `r₀` and
every return address `ra`. -/
@[ascend] theorem wrp_call_withRa {f : Label} {g : Fragment} (hg : FunDecls.at (label f) = some g)
    (asz osz : Width) {k : BitVec 64 → Int64 → BlockM MachineData Unit}
    (hk : ∀ r₀ ra, ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ g.prog
      ⪯[ofStateRel (JRel Mem.Sub)] (k r₀ ra) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄)
    {Q : Unit → Unit → MachineData → Prop} {E : Int64 → Int64 → MachineData → Prop} :
    (fun _ => (∀ t, Q () () t) ∧ ∀ l t, E l l t)
      ⊑ wrp (ofStateRel (JRel Mem.Sub))
          (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
          (withRa k) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred] at hs
  obtain ⟨⟨hQ, hE⟩, a, hJ, hw⟩ := hs
  rw [wp_BlockM_eq, withRa_run] at hw
  cases hr : withRaRun k a with
  | none => rw [hr] at hw; exact hw.elim
  | some r =>
  rw [hr] at hw
  obtain ⟨hm, hall⟩ := withRa_some hr
  have hrsp : a.regs.get64 .rsp = s.regs.get64 .rsp := by rw [JRel.regs hJ]
  refine (Program.WP.wp_call_iff hg).mpr fun [h : Embeds _] => ?_
  let ra := h.embedding.endAddr
  refine ⟨?_, ?_⟩
  · have := hJ.2.2.2.loadInt_isSome hm
    rwa [hrsp, abs_dmem] at this
  rw [FunDecls.body_eq hg]
  obtain ⟨a', b, hrun, hro⟩ := callOutcome_of_run (hall ra)
  let Qa' : Unit → MachineData → Prop := fun _ _ => False
  let Ea' : (Int64 → MachineData → Prop) × EStack⟨⟩ :=
    (fun l b' => (k (a.regs.get64 .rsp - 8#64) ra).run.run (a.push64 ra) = some (.error l, b'), estack⟨⟩)
  have hwk : wp (k (a.regs.get64 .rsp - 8#64) ra) Qa' Ea' (a.push64 ra) := by
    rw [wp_BlockM_eq, hrun]
    exact hrun
  have hc := wrp_transport (hk (s.regs.get64 .rsp - 8#64) ra).le_wrp Qa' Ea' (s.push64 ra)
    (by
      simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
      refine ⟨⟨?_, MachineData.retAddr_push64 s ra⟩, a.push64 ra, jsub_push64 hJ ra, ?_⟩
      · simp only [MachineData.regs_push64, Reg64s.get64_set64, reduceIte]
      · rw [← hrsp]; exact hwk)
  refine Program.wp_mono (fun u hu => ?_) (fun u hu => ?_) hc
  · simp only [Concretization.post_pi, ofStateRel_pred, Qa', and_false, exists_false] at hu
  · simp only [ePosts_ret, Concretization.post_pi, ofStateRel_pred, AddrRel] at hu
    obtain ⟨l, rfl, b', hJb, hb'⟩ := hu
    have hb'' : (k (a.regs.get64 .rsp - 8#64) ra).run.run (a.push64 ra) = some (.error u.pc, b') := hb'
    rw [hrun] at hb''
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hb'')
    injection h1 with h1
    subst h1 h2 hro
    split
    · rename_i hl
      rw [if_pos hl] at hw
      simp only [Concretization.post_pi, ofStateRel_pred]
      refine ⟨(), hQ _, _, ?_, hw⟩
      rw [hrsp]
      exact jsub_eraseSlot hJb _
    · rename_i hl
      rw [if_neg hl] at hw
      simp only [ePosts_ret, Concretization.post_pi, ofStateRel_pred]
      refine ⟨_, hE _ _, _, ?_, hw⟩
      rw [hrsp]
      exact jsub_eraseSlot hJb _

end

/-! ## `withRa` never throws

If the common outcome of `withRa k` were an exit to `a`, the return address `ra = a` would turn
that exit into a return. So `withRa k` returns or is undefined behaviour. -/

theorem withRaRun_ne_error {k : BitVec 64 → Int64 → BlockM MachineData Unit} {s t : MachineData}
    {a : Int64} : withRaRun k s ≠ some (.error a, t) := fun h => by
  obtain ⟨-, hall⟩ := withRa_some h
  obtain ⟨a', b, -, hr⟩ := callOutcome_of_run (hall a)
  by_cases ha : a' = a
  · rw [if_pos ha] at hr
    exact nomatch (Prod.mk.inj hr).1
  · rw [if_neg ha] at hr
    injection (Prod.mk.inj hr).1 with h'
    exact ha h'.symm

theorem wp_withRa {k : BitVec 64 → Int64 → BlockM MachineData Unit} (Q : Unit → MachineData → Prop)
    (E E' : (Int64 → MachineData → Prop) × EStack⟨⟩) (s : MachineData) :
    wp (withRa k) Q E s = wp (withRa k) Q E' s := by
  rw [wp_BlockM_eq, wp_BlockM_eq, withRa_run]
  cases h : withRaRun k s with
  | none => rfl
  | some r =>
    obtain ⟨e, t⟩ := r
    cases e with
    | ok u => rfl
    | error a => exact absurd h withRaRun_ne_error

theorem ThrowsOnly.withRa {P : Int64 → MachineData → Prop} (k : BitVec 64 → Int64 → BlockM MachineData Unit) :
    Ascent.ThrowsOnly P (withRa k) = True := eq_true fun Q E s hw => by
  rw [wp_withRa Q _ E s]
  exact hw

theorem tryCatch_withRa_bind {β : Type} (k : BitVec 64 → Int64 → BlockM MachineData Unit)
    (f : Unit → BlockM MachineData β) (h : Int64 → BlockM MachineData β) :
    tryCatch (withRa k >>= f) h = withRa k >>= fun u => tryCatch (f u) h := by
  have hmono : ∀ (Q : β → MachineData → Prop) (E : (Int64 → MachineData → Prop) × EStack⟨⟩) u t,
      wp (f u) Q (fun l => wp (h l) Q E, E.2) t ↔ wp (tryCatch (f u) h) Q E t :=
    fun Q E u t => by rw [BlockLoop.wp_tryCatch]
  apply BlockLoop.ext_wp <;> intro Q E s hw <;>
    simp only [BlockLoop.wp_tryCatch, WPMonadExact.wp_bind_eq] at hw ⊢
  · rw [wp_withRa _ _ E s] at hw
    exact WP.wp_monotone_post (x := withRa k) (fun u t h' => (hmono Q E u t).mp h') s hw
  · rw [wp_withRa _ _ (fun l => wp (h l) Q E, E.2) s]
    rw [wp_withRa _ _ (fun l => wp (h l) Q E, E.2) s] at hw
    exact WP.wp_monotone_post (x := withRa k) (fun u t h' => (hmono Q E u t).mpr h') s hw
end Ascent.Kraken
