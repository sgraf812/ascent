import Demo.L1

/-!
# The first layer under a sub-map relation

`a ≼ b` states that the machine states `a` and `b` agree on the registers and the flags, and that
each mapped byte of `a` holds the same value in `b`. `Jsub t a := a ≼ abs t` relates a concrete state
`t` to every abstract state that forgets some of its memory. A call erases the return slot from the
abstract state: the slot holds a different address for each return address that the call pushes.

`MonoRun x` states that the abstract program `x` runs on a smaller state to a smaller state with the
same result. Under it, a refinement under `ofStateRepr abs` is a refinement under `ofStateRel Jsub`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRel ofStateRepr_pred ofStateRel_pred)
open scoped Program.WP

namespace Ascent.Kraken

/-- The memory `m` is a sub-map of `m'`. -/
def Mem.Sub (m m' : DataMem) : Prop := ∀ p v, m.get? p = some v → m'.get? p = some v

/-- `a ≼ b`: `a` agrees with `b` on the registers and the flags, and the memory of `a` is a sub-map
of the memory of `b`. -/
def MachineData.Sub (a b : MachineData) : Prop :=
  a.regs = b.regs ∧ a.zmms = b.zmms ∧ a.status = b.status ∧ Mem.Sub a.dmem b.dmem

scoped infix:50 " ≼ " => MachineData.Sub

/-- The concrete state `t` and an abstract state `a` that forgets some memory of `abs t`. -/
def Jsub (t a : MachineData) : Prop := a ≼ abs t

theorem Mem.Sub.refl (m : DataMem) : Mem.Sub m m := fun _ _ h => h

theorem MachineData.Sub.refl (a : MachineData) : a ≼ a := ⟨rfl, rfl, rfl, Mem.Sub.refl _⟩

theorem Mem.Sub.trans {m₁ m₂ m₃ : DataMem} (h₁ : Mem.Sub m₁ m₂) (h₂ : Mem.Sub m₂ m₃) : Mem.Sub m₁ m₃ :=
  fun p v h => h₂ p v (h₁ p v h)

theorem MachineData.Sub.trans {a b c : MachineData} (h₁ : a ≼ b) (h₂ : b ≼ c) : a ≼ c :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.trans h₂.2.2.2⟩

theorem jsub_regs {t a : MachineData} (h : Jsub t a) : a.regs = t.regs := h.1

/-! ## Monotone abstract programs -/

/-- The abstract program `x` runs on a smaller state to a smaller state with the same result, and
runs at all on the larger state whenever it runs on the smaller one. -/
def MonoRun {α : Type} (x : BlockM MachineData α) : Prop :=
  ∀ a b, a ≼ b → ∀ r, x.run.run a = some r → ∃ r', x.run.run b = some r' ∧ r.1 = r'.1 ∧ r.2 ≼ r'.2

theorem MonoRun.wp {α : Type} {x : BlockM MachineData α} (hx : MonoRun x) {a b : MachineData}
    (hab : a ≼ b) {Q : α → MachineData → Prop} {E : (Int64 → MachineData → Prop) × EStack⟨⟩}
    (h : wp x Q E a) :
    wp x (fun v b' => ∃ a', a' ≼ b' ∧ Q v a') (fun l b' => ∃ a', a' ≼ b' ∧ E.1 l a', E.2) b := by
  rw [wp_BlockM_eq] at h ⊢
  revert h
  cases hr : x.run.run a with
  | none => intro h; exact h.elim
  | some r =>
    intro h
    obtain ⟨r', hr', h1, h2⟩ := hx a b hab r hr
    rw [hr']
    obtain ⟨e, s⟩ := r
    obtain ⟨e', s'⟩ := r'
    simp only at h1 h2
    subst h1
    cases e with
    | error l => exact ⟨s, h2, h⟩
    | ok v => exact ⟨s, h2, h⟩

/-- A refinement under `ofStateRepr abs` with a monotone abstract program is a refinement under
`ofStateRel Jsub`. -/
theorem wrp_rel_of_abs {CProg : Type} {CVal AV : Type} [WP CProg CVal (MachineData → Prop) (Int64 → MachineData → Prop)]
    {c : CProg} {x : BlockM MachineData AV} {P : MachineData → Prop}
    {Q : CVal → AV → MachineData → Prop} {E : Int64 → Int64 → MachineData → Prop}
    (hx : MonoRun x) (h : P ⊑ wrp (ofStateRepr abs) c x Q E) :
    P ⊑ wrp (ofStateRel Jsub) c x Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred] at ht
  obtain ⟨hP, a, hJ, ha⟩ := ht
  have hb := hx.wp hJ ha
  have hc := wrp_transport h (fun v b' => ∃ a', a' ≼ b' ∧ Qa v a')
    (fun l b' => ∃ a', a' ≼ b' ∧ Ea.1 l a', Ea.2) t
    (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ⟨hP, hb⟩)
  refine (WP.wp_monotone (x := c) ?_ ?_) t hc
  · intro v t' h'
    simp only [Concretization.post_pi, ofStateRepr_pred, ofStateRel_pred] at h' ⊢
    obtain ⟨av, hq, a', hsub, hqa⟩ := h'
    exact ⟨av, hq, a', hsub, hqa⟩
  · intro l t' h'
    simp only [ePosts_ret, Concretization.post_pi, ofStateRepr_pred, ofStateRel_pred] at h' ⊢
    obtain ⟨av, hq, a', hsub, hqa⟩ := h'
    exact ⟨av, hq, a', hsub, hqa⟩

/-! ## Memory facts of the sub-map relation -/

theorem Mem.Sub.storeInt {m m' : DataMem} (h : Mem.Sub m m') (a : BitVec 64) (n : Nat) (v : Int) :
    Mem.Sub (m.storeInt a n v) (m'.storeInt a n v) := fun p x hp => by
  rw [Mem.get?_storeInt] at hp ⊢
  cases hb : ((Int.toBytes n v).At a)[p]? with
  | some y => rw [hb] at hp; exact hp
  | none => rw [hb] at hp; exact h p x hp

theorem Mem.Sub.loadBytes {m m' : DataMem} (h : Mem.Sub m m') {a : BitVec 64} {n : Nat}
    {bs : List UInt8} (hl : m.loadBytes a n = some bs) : m'.loadBytes a n = some bs := by
  rw [Mem.loadBytes_eq_some_iff] at hl ⊢
  exact ⟨hl.1, fun i hi => h _ _ (hl.2 i hi)⟩

theorem Mem.Sub.loadInt {m m' : DataMem} (h : Mem.Sub m m') {a : BitVec 64} {n : Nat} {v : Int}
    (hl : m.loadInt a n = some v) : m'.loadInt a n = some v := by
  simp only [Mem.loadInt, Option.map_eq_some_iff] at hl ⊢
  obtain ⟨bs, hbs, rfl⟩ := hl
  exact ⟨bs, h.loadBytes hbs, rfl⟩

theorem Mem.Sub.loadInt_isSome {m m' : DataMem} (h : Mem.Sub m m') {a : BitVec 64} {n : Nat}
    (hl : (m.loadInt a n).isSome = true) : (m'.loadInt a n).isSome = true := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
  rw [h.loadInt hv]
  rfl

theorem jsub_push64 {s a : MachineData} (h : Jsub s a) (ra : Int64) : Jsub (s.push64 ra) (a.push64 ra) := by
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

theorem jsub_eraseSlot {t b : MachineData} (h : Jsub t b) (r : BitVec 64) : Jsub t (eraseSlot r b) :=
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
      ⪯[ofStateRel Jsub] (k r₀ ra) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄)
    {Q : Unit → Unit → MachineData → Prop} {E : Int64 → Int64 → MachineData → Prop} :
    (fun _ => (∀ t, Q () () t) ∧ ∀ l t, E l l t)
      ⊑ wrp (ofStateRel Jsub)
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
  have hrsp : a.regs.get64 .rsp = s.regs.get64 .rsp := by rw [jsub_regs hJ]
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

end Ascent.Kraken
