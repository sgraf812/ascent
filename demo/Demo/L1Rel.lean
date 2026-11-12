import Demo.L1Gen
import Demo.WithRa

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

/-- The guard of a call: the return slot below the stack pointer is mapped. -/
def slotOk (s : MachineData) : Prop := (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true

/-- The call of the abstract function `k` at the first layer: `k` runs with the frame `rsp - 8`
from the state with the return address pushed, and the return erases the return slot. -/
noncomputable def withRa (k : BitVec 64 → Int64 → BlockM MachineData Unit) : BlockM MachineData Unit :=
  withRaOn slotOk (fun s ra => s.push64 ra) (fun s t => eraseSlot (s.regs.get64 .rsp) t)
    (fun s => k (s.regs.get64 .rsp - 8#64))

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
  rw [wp_BlockM_eq, withRa, withRaOn_run] at hw
  cases hr : withRaOnRun slotOk (fun s ra => s.push64 ra) (fun s t => eraseSlot (s.regs.get64 .rsp) t)
      (fun s => k (s.regs.get64 .rsp - 8#64)) a with
  | none => rw [hr] at hw; exact hw.elim
  | some r =>
  rw [hr] at hw
  obtain ⟨hm, hall⟩ := withRaOn_some hr
  have hrsp : a.regs.get64 .rsp = s.regs.get64 .rsp := by rw [JRel.regs hJ]
  refine (Program.WP.wp_call_iff hg).mpr fun [h : Embeds _] => ?_
  let ra := h.embedding.endAddr
  refine ⟨?_, ?_⟩
  · have := hJ.2.2.2.loadInt_isSome hm
    rwa [hrsp, abs_dmem] at this
  rw [FunDecls.body_eq hg]
  obtain ⟨a', b, hrun, hro⟩ := callOutcomeOn_of_run (hall ra)
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

theorem ThrowsOnly.withRa {P : Int64 → MachineData → Prop} (k : BitVec 64 → Int64 → BlockM MachineData Unit) :
    Ascent.ThrowsOnly P (withRa k) = True := ThrowsOnly.withRaOn

theorem tryCatch_withRa_bind {β : Type} (k : BitVec 64 → Int64 → BlockM MachineData Unit)
    (f : Unit → BlockM MachineData β) (h : Int64 → BlockM MachineData β) :
    tryCatch (withRa k >>= f) h = withRa k >>= fun u => tryCatch (f u) h :=
  tryCatch_withRaOn_bind f h

end Ascent.Kraken
