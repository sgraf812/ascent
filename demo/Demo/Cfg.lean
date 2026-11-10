import Demo.Kraken
import Ascent.Table
import Ascent.BlockLoop
import Kraken.StateCfg
import Ascent.UB.StateT
import Ascent.UB.WhileLoop
import Ascent.Refinement.Lockstep

/-!
# Control-flow graphs

`cfgLoop (Program.table p cell) .entry` is the abstract program of a kraken text `p` with labels:
the block loop of `Ascent.BlockLoop` over the table of the text, whose block at a label runs the
abstract cell of the label and then jumps to its successor in the text. A block program lives in
`BlockM Aσ`, and a jump is the exception that carries its target; the return of the text is a jump
to `.exit`, which has no block.

`refines_cfg` refines a text to that loop from one refinement per block, in the form of kraken's
funspec: the text starts at `s.push64 ra`, and its return pairs with the abstract exception `.exit`
through `RetRel s ra`.
-/

open Std.WP Lean.Order Ascent
open scoped Program.WP

/-! ## Labels of the abstract control flow

A kraken block carries an optional label (`none` for the entry block) and an optional successor
(`none` for the end of the text). `CfgLabel` names the places of the abstract control flow: the
entry, a labelled block, the exit, and the exit with a return value `ret v`, which a layer above the
machine uses to carry the value of the return register out of the function. -/

inductive CfgLabel where
  | entry
  | label (l : Label)
  | exit
  | ret (v : BitVec 64)
  deriving DecidableEq, Repr

def CfgLabel.ofLabel : Option Label → CfgLabel
  | none => .entry
  | some l => .label l

def CfgLabel.ofNext : Option Label → CfgLabel
  | none => .exit
  | some l => .label l

@[vcgen_simp, grind =] theorem CfgLabel.ofLabel_none : CfgLabel.ofLabel none = .entry := rfl
@[vcgen_simp, grind =] theorem CfgLabel.ofLabel_some (l : Label) : CfgLabel.ofLabel (some l) = .label l := rfl
@[vcgen_simp, grind =] theorem CfgLabel.ofNext_none : CfgLabel.ofNext none = .exit := rfl
@[vcgen_simp, grind =] theorem CfgLabel.ofNext_some (l : Label) : CfgLabel.ofNext (some l) = .label l := rfl

theorem CfgLabel.ofLabel_ne_exit : ∀ b : Option Label, CfgLabel.ofLabel b ≠ .exit
  | none => nofun
  | some _ => nofun

attribute [vcgen_simp] Program.straight_nil Program.straight_cons_instr Program.straight_cons_label
  Program.straight_cons_byteArray

/-! ## The table of blocks of a text -/

theorem Program.label_mem_blocksFrom {b : Option Label} :
    ∀ {j : Nat} {body : Program} {bs : List (Label × Program)} {blk : Program.Block},
      blk ∈ Program.blocksFrom b j body bs → blk.label = b ∨ ∃ lb ∈ bs, blk.label = some lb.1
  | _, _, [], blk, h => by
    simp only [Program.blocksFrom, List.mem_singleton] at h
    subst h
    exact Or.inl rfl
  | j, body, (l, body') :: bs, blk, h => by
    simp only [Program.blocksFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inl rfl
    · rcases Program.label_mem_blocksFrom h with h | ⟨lb, hlb, h⟩
      · exact Or.inr ⟨(l, body'), List.mem_cons_self, h⟩
      · exact Or.inr ⟨lb, List.mem_cons_of_mem _ hlb, h⟩

theorem Program.find?_blocksFrom {b : Option Label} :
    ∀ {j : Nat} {body : Program} {bs : List (Label × Program)}, (bs.map (·.1)).Nodup →
      (∀ lb ∈ bs, b ≠ some lb.1) → ∀ {blk : Program.Block}, blk ∈ Program.blocksFrom b j body bs →
        (Program.blocksFrom b j body bs).find?
          (fun blk' => CfgLabel.ofLabel blk'.label = CfgLabel.ofLabel blk.label) = some blk
  | _, _, [], _, _, blk, h => by
    simp only [Program.blocksFrom, List.mem_singleton] at h
    subst h
    simp [Program.blocksFrom]
  | j, body, (l, body') :: bs, hnd, hb, blk, h => by
    simp only [Program.blocksFrom, List.mem_cons] at h
    rcases h with rfl | h
    · simp [Program.blocksFrom]
    · have hne : b ≠ blk.label := by
        rcases Program.label_mem_blocksFrom h with h' | ⟨lb, hlb, h'⟩
        · rw [h']; exact hb (l, body') List.mem_cons_self
        · rw [h']; exact hb lb (List.mem_cons_of_mem _ hlb)
      have hne' : CfgLabel.ofLabel b ≠ CfgLabel.ofLabel blk.label := by
        cases b <;> cases hbl : blk.label <;> simp_all [CfgLabel.ofLabel]
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      rw [Program.blocksFrom, List.find?_cons_of_neg (by simpa using hne')]
      exact Program.find?_blocksFrom hnd.2
        (fun lb hlb heq => hnd.1 ⟨lb, hlb, (Option.some.inj heq).symm⟩) h

/-- The jump at the end of a block that falls through to its successor `next`: a normal end at the
end of the text. -/
def jumpTo {Aσ : Type} : Option Label → ExceptT CfgLabel (StateT Aσ UB) Unit
  | none => pure ()
  | some l => throw (.label l)

@[vcgen_simp] theorem jumpTo_none {Aσ : Type} :
    (jumpTo none : ExceptT CfgLabel (StateT Aσ UB) Unit) = pure () := rfl
@[vcgen_simp] theorem jumpTo_some {Aσ : Type} (l : Label) :
    (jumpTo (some l) : ExceptT CfgLabel (StateT Aσ UB) Unit) = throw (.label l) := rfl

/-- The table of a text: the block of each label runs its cell and then falls through to its
successor in the text. -/
def Program.table {Aσ : Type} (p : Program) (cell : CfgLabel → ExceptT CfgLabel (StateT Aσ UB) Unit) :
    Table CfgLabel (ExceptT CfgLabel (StateT Aσ UB) Unit) :=
  (Program.blocks p).map fun blk =>
    (CfgLabel.ofLabel blk.label, cell (CfgLabel.ofLabel blk.label) >>= fun _ => jumpTo blk.next)

theorem Table.get?_map {κ α β : Type} [DecidableEq κ] (bs : List α) (key : α → κ) (val : α → β) (k : κ) :
    Table.get? (bs.map fun a => (key a, val a)) k = (bs.find? fun a => key a = k).map val := by
  induction bs with
  | nil => rfl
  | cons a bs ih =>
    rw [List.map_cons, Table.get?_cons, ih]
    by_cases h : k = key a
    · simp [h]
    · have h' : ¬ key a = k := fun e => h e.symm
      simp [h, h']

theorem Program.table_get? {Aσ : Type} {p : Program} (hnd : (Program.labels p).Nodup)
    (cell : CfgLabel → ExceptT CfgLabel (StateT Aσ UB) Unit) {blk : Program.Block}
    (h : blk ∈ Program.blocks p) :
    (Program.table p cell).get? (CfgLabel.ofLabel blk.label)
      = some (cell (CfgLabel.ofLabel blk.label) >>= fun _ => jumpTo blk.next) := by
  rw [Program.labels_view] at hnd
  rw [Program.table, Table.get?_map]
  have := Program.find?_blocksFrom hnd (fun _ _ => by simp) h
  unfold Program.blocks
  rw [this]
  rfl

theorem Program.table_get?_exit {Aσ : Type} (p : Program)
    (cell : CfgLabel → ExceptT CfgLabel (StateT Aσ UB) Unit) :
    (Program.table p cell).get? .exit = none := by
  rw [Program.table, Table.get?_map, List.find?_eq_none.mpr]
  · rfl
  · intro blk _ h
    exact CfgLabel.ofLabel_ne_exit blk.label (of_decide_eq_true h)

namespace Ascent.Kraken

/-! ## The abstract control-flow loop -/

abbrev BlockM (Aσ : Type) := ExceptT CfgLabel (StateT Aσ UB)

/-! ## The run of a block program -/

theorem wp_BlockM_eq {Aσ α : Type} (x : BlockM Aσ α) (Qa : α → Aσ → Prop)
    (Ea : (CfgLabel → Aσ → Prop) × EStack⟨⟩) (st : Aσ) :
    wp x Qa Ea st = match x.run.run st with
      | none => False
      | some (.ok a, st') => Qa a st'
      | some (.error e, st') => Ea.1 e st' := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq]
  rcases hx : x.run.run st with _ | ⟨l' | a, st'⟩
  · exact bot_prop_eq
  · rfl
  · rfl

theorem UB.some_bind {α β : Type} (a : α) (f : α → UB β) : (Bind.bind (m := UB) (some a) f) = f a := rfl
theorem UB.map_some {α β : Type} (g : α → β) (a : α) :
    (Functor.map (f := UB) g (some a)) = some (g a) := rfl
theorem UB.pure_eq {α : Type} (a : α) : (pure a : UB α) = some a := rfl
theorem UB.fail_eq {α : Type} : (UB.fail : UB α) = none := rfl
theorem UB.bind_eq_some {α β : Type} (x : UB α) (f : α → UB β) (b : β) :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b := Option.bind_eq_some_iff
theorem UB.map_eq_some {α β : Type} (g : α → β) (x : UB α) (b : β) :
    (g <$> x) = some b ↔ ∃ a, x = some a ∧ g a = b := Option.map_eq_some_iff

section
variable {σ α : Type}

theorem wp_get_bind (k : σ → BlockM σ α) (Q : α → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩)
    (s : σ) : wp (get >>= k) Q E s = wp (k s) Q E s := by
  rw [wp_BlockM_eq, wp_BlockM_eq]
  rfl

theorem wp_get (Q : σ → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (get : BlockM σ σ) Q E s = Q s s := by
  rw [wp_BlockM_eq]
  rfl

theorem wp_throw_block (l : CfgLabel) (Q : α → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩)
    (s : σ) : wp (throw l : BlockM σ α) Q E s = E.1 l s := by
  rw [wp_BlockM_eq]
  rfl

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


/-! ## The block relations -/

def RetRel (s : MachineData) (ra : Int64) : Int64 → CfgLabel → MachineData → Prop :=
  fun a l' s' => a = ra ∧ l' = .exit ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp

@[grind norm] theorem RetRel_eq (s : MachineData) (ra a : Int64) (l : CfgLabel) (s' : MachineData) :
    RetRel s ra a l s' = (a = ra ∧ l = .exit ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp) := rfl

/-- The stack discipline inside the function: the stack pointer and the return slot of the entry
state `s₀`. -/
def SameStackFrame (s₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = s₀.regs.get64 .rsp ∧ s.retAddr = s₀.retAddr

def FallRel (s₀ : MachineData) : Unit → Unit → MachineData → Prop := fun _ _ s => SameStackFrame s₀ s

def JumpRel [Host] (p : Program) (s₀ : MachineData) : Int64 → CfgLabel → MachineData → Prop :=
  fun a l' s =>
    (∃ l, l ∈ Program.labels p ∧ l' = .label l ∧ a = label l ∧ SameStackFrame s₀ s)
    ∨ (l' = .exit ∧ a = s₀.retAddr.get! ∧ s.regs.get64 .rsp = s₀.regs.get64 .rsp + 8#64)

theorem SameStackFrame.of_step {s₀ t s' : MachineData} (h : SameStackFrame s₀ t)
    (hrsp : s'.regs.get64 .rsp = t.regs.get64 .rsp)
    (hmem : Mem.loadInt s'.dmem (t.regs.get64 .rsp) 8 = Mem.loadInt t.dmem (t.regs.get64 .rsp) 8) :
    SameStackFrame s₀ s' := by
  refine ⟨hrsp.trans h.1, ?_⟩
  rw [MachineData.retAddr_eq, hrsp, hmem, ← MachineData.retAddr_eq]
  exact h.2

theorem FallRel.intro {s₀ s : MachineData} (h : SameStackFrame s₀ s) : FallRel s₀ () () s := h

theorem JumpRel.internal [Host] {p : Program} {s₀ s : MachineData} {a : Int64} {l : Label}
    (hmem : l ∈ Program.labels p) (ha : a = label l) (h : SameStackFrame s₀ s) :
    JumpRel p s₀ a (.label l) s :=
  Or.inl ⟨l, hmem, rfl, ha, h⟩

theorem JumpRel.exit [Host] {p : Program} {s₀ s : MachineData} {a : Int64}
    (ha : a = s₀.retAddr.get!) (hrsp : s.regs.get64 .rsp = s₀.regs.get64 .rsp + 8#64) :
    JumpRel p s₀ a .exit s :=
  Or.inr ⟨rfl, ha, hrsp⟩

noncomputable instance {Aσ : Type} :
    EPostsConcretization (MachineData → Prop) (Aσ → Prop) (Int64 → MachineData → Prop)
      ((CfgLabel → Aσ → Prop) × EStack⟨⟩) (Int64 → CfgLabel → MachineData → Prop) where
  ePosts γ E Ea := γ.post E Ea.1

@[simp, grind norm] theorem ePosts_ret {Aσ : Type} (γ : Concretization (MachineData → Prop) (Aσ → Prop))
    (E : Int64 → CfgLabel → MachineData → Prop) (Ea : (CfgLabel → Aσ → Prop) × EStack⟨⟩) :
    EPostsConcretization.ePosts (CEPosts := Int64 → MachineData → Prop) γ E Ea = γ.post E Ea.1 := rfl

/-! ## The control-flow rule -/

theorem BlockM.run_bind {Aσ α β : Type} (x : BlockM Aσ α) (k : α → BlockM Aσ β) (st : Aσ) :
    (x >>= k).run.run st = (x.run.run st >>= fun p =>
      match p.1 with
      | .ok a => (k a).run.run p.2
      | .error e => pure (.error e, p.2)) := by
  rw [ExceptT.run_bind, StateT.run_bind]
  congr 1
  funext p
  rcases p with ⟨_ | _, _⟩ <;> rfl

section
variable {Aσ : Type} (abs : MachineData → Aσ)

theorem decreases_of_steps_lt {T : Table CfgLabel (BlockM Aσ Unit)}
    {l : Option Label} {b : Label} {i j : Nat} {t s : MachineData}
    (h : steps T (.label b) (abs s) < steps T (CfgLabel.ofLabel l) (abs t)) :
    Program.Decreases (fun l t => steps T (.label l) (abs t)) l i t b j s := by
  cases l with
  | none => trivial
  | some l => exact Or.inl h

end

section
variable [Host] [FunDecls] {Aσ : Type} (abs : MachineData → Aσ)

theorem wrp_cfg_le {p : Program} (hnd : (Program.labels p).Nodup)
    {cell : CfgLabel → BlockM Aσ Unit} {s : MachineData} {ra : Int64}
    (h : ∀ blk ∈ Program.blocks p, ∀ t, SameStackFrame (s.push64 ra) t →
      ⦃(· = t)⦄ blk.body ⪯[Concretization.ofStateRepr abs] (cell (CfgLabel.ofLabel blk.label))
        ⦃FallRel (s.push64 ra); JumpRel p (s.push64 ra)⦄) :
    (fun t => t = s.push64 ra) ⊑ wrp (Concretization.ofStateRepr abs) p
      (cfgLoop (Program.table p cell) .entry) (fun _ _ => ⊤) (RetRel s ra) := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred] at ht
  obtain ⟨rfl, hpre⟩ := ht
  let T := Program.table p cell
  let I : Program.CfgInvariant := fun {_} l t =>
    wp (cfgLoop T (.label l)) Qa Ea (abs t) ∧ SameStackFrame (s.push64 ra) t
  let Q : Unit → MachineData → Prop := fun _ u =>
    (Concretization.ofStateRepr abs).post (fun _ _ => ⊤) Qa () u
  let var : Program.CfgVariant := fun l t => steps T (.label l) (abs t)
  refine Program.WP.cfg (p := p) (Q := Q)
    (E := EPostsConcretization.ePosts (Concretization.ofStateRepr abs) (RetRel s ra) Ea)
    (s₀ := s.push64 ra) @I var ?_
  intro blk hmem t hI
  have hIt : wp (cfgLoop T (CfgLabel.ofLabel blk.label)) Qa Ea (abs t)
      ∧ SameStackFrame (s.push64 ra) t := by
    cases hl : blk.label with
    | none =>
      rw [hl] at hI
      change t = s.push64 ra at hI
      subst hI
      exact ⟨hpre, rfl, rfl⟩
    | some l =>
      rw [hl] at hI
      exact hI
  obtain ⟨hIt, hst⟩ := hIt
  have hTb : T.get? (CfgLabel.ofLabel blk.label)
      = some (cell (CfgLabel.ofLabel blk.label) >>= fun _ => jumpTo blk.next) :=
    Program.table_get? hnd cell hmem
  have hfix : ∃ r, cfgFix T (CfgLabel.ofLabel blk.label) (abs t) = some r := by
    rw [wp_BlockM_eq, cfgLoop_run] at hIt
    revert hIt
    cases cfgFix T (CfgLabel.ofLabel blk.label) (abs t) <;> intro hIt
    · exact hIt.elim
    · exact ⟨_, rfl⟩
  obtain ⟨r, hfix⟩ := hfix
  rw [wp_cfgLoop_some T Qa Ea _ hTb, WPMonadExact.wp_bind_eq, wp_BlockM_eq] at hIt
  let c := cell (CfgLabel.ofLabel blk.label)
  let H : (CfgLabel → Aσ → Prop) × EStack⟨⟩ := (fun l' => wp (cfgLoop T l') Qa Ea, Ea.2)
  let Qa' : Unit → Aσ → Prop := fun _ st' =>
    wp (jumpTo blk.next : BlockM Aσ Unit) Qa H st' ∧ c.run.run (abs t) = some (.ok (), st')
  let Ea' : (CfgLabel → Aσ → Prop) × EStack⟨⟩ :=
    (fun l' st' => wp (cfgLoop T l') Qa Ea st' ∧ c.run.run (abs t) = some (.error l', st'), Ea.2)
  have hpre' : wp c Qa' Ea' (abs t) := by
    rw [wp_BlockM_eq]
    revert hIt
    rcases hrun : c.run.run (abs t) with _ | ⟨l' | _, st'⟩ <;> intro hIt
    · exact hIt.elim
    · exact ⟨hIt, hrun⟩
    · exact ⟨hIt, hrun⟩
  have hb := wrp_transport (h blk hmem t hst).le_wrp Qa' Ea'
  have hmeet : ((fun t' => t' = t) ⊓ (Concretization.ofStateRepr abs).pred (wp c Qa' Ea')) t := by
    simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]
    exact ⟨trivial, hpre'⟩
  have hwp := hb t hmeet
  refine Program.wp_mono (fun u hu => ?_) (fun u hu => ?_) hwp
  · change (Concretization.ofStateRepr abs).post (FallRel (s.push64 ra)) Qa' () u.data at hu
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
      meet_prop_eq_and, Concretization.ofStateRepr_pred, FallRel] at hu
    obtain ⟨-, hst', hQ, hrun⟩ := hu
    show Program.Next @I (s.push64 ra) Q
      (Program.Decreases var blk.label blk.idx t) blk.next (blk.idx + 1) u.data
    cases hn : blk.next with
    | none =>
      rw [hn, jumpTo_none, WPMonadExact.wp_pure_eq] at hQ
      simp only [Program.Next, Q, Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, top_apply, top_prop_eq, Concretization.ofStateRepr_pred]
      exact ⟨(), trivial, hQ⟩
    | some l' =>
      rw [hn, jumpTo_some, wp_throw_block] at hQ
      refine ⟨⟨hQ, hst'⟩, decreases_of_steps_lt abs ?_⟩
      have hb' : (c >>= fun _ => jumpTo blk.next).run.run (abs t)
          = some (.error (.label l'), abs u.data) := by
        rw [BlockM.run_bind, hrun, hn]
        rfl
      exact steps_lt T hTb hb' hfix
  · show Program.Intercept (Program.labels p) (s.push64 ra)
      (fun l j s' => I (s₀ := s.push64 ra) l s' ∧ Program.Decreases var blk.label blk.idx t l j s')
      (EPostsConcretization.ePosts (Concretization.ofStateRepr abs) (RetRel s ra) Ea)
      u.pc u.data
    change (Concretization.ofStateRepr abs).post (JumpRel p (s.push64 ra)) Ea'.1
      u.pc u.data at hu
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
      meet_prop_eq_and, Concretization.ofStateRepr_pred, JumpRel] at hu
    obtain ⟨l', hrel, hE, hrun⟩ := hu
    have hb' : (c >>= fun _ => jumpTo blk.next).run.run (abs t) = some (.error l', abs u.data) := by
      rw [BlockM.run_bind, hrun]
      rfl
    rcases hrel with ⟨l, hmem', rfl, ha, hst'⟩ | ⟨rfl, ha, hrsp'⟩
    · refine Program.Intercept.intro (Or.inl ⟨?_, l, ha.symm, hmem', ⟨hE, hst'⟩, ?_⟩)
      · show ¬ ((s.push64 ra).regs.get64 .rsp).SerialLt (u.data.regs.get64 .rsp)
        rw [hst'.1]
        exact BitVec.not_serialLt_self _
      · exact decreases_of_steps_lt abs (steps_lt T hTb hb' hfix)
    · rw [wp_cfgLoop_none T Qa Ea _ (Program.table_get?_exit p cell)] at hE
      have hrsp₀ : (s.push64 ra).regs.get64 .rsp = s.regs.get64 .rsp - 8#64 := by
        simp only [MachineData.regs_push64, Reg64s.get64_set64, ↓reduceIte]
      refine Program.Intercept.intro (Or.inr ⟨?_, fun _ _ _ => ?_⟩)
      · show (Concretization.ofStateRepr abs).post (RetRel s ra) Ea.1 u.pc u.data
        simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
          meet_prop_eq_and, Concretization.ofStateRepr_pred, RetRel]
        refine ⟨.exit, ⟨?_, rfl, ?_⟩, hE⟩
        · rw [ha, MachineData.retAddr_push64, Option.get!_some]
        · rw [hrsp', hrsp₀, BitVec.sub_add_cancel]
      · show ((s.push64 ra).regs.get64 .rsp).SerialLt (u.data.regs.get64 .rsp)
        rw [hrsp', hrsp₀, BitVec.sub_add_cancel]
        exact BitVec.serialLt_sub _ _ (by decide)

/-! ## The grind theory of the block relations

Shape equations at a literal label, in the style of kraken's flag and register theories, so that a
grind finisher normalizes a relation VC without a disjunction to split on. -/

@[simp, vcgen_simp] theorem FallRel_eq (s₀ s : MachineData) : FallRel s₀ () () s = SameStackFrame s₀ s := rfl

@[simp, vcgen_simp] theorem SameStackFrame_eq (s₀ s : MachineData) :
    SameStackFrame s₀ s = (s.regs.get64 .rsp = s₀.regs.get64 .rsp ∧ s.retAddr = s₀.retAddr) := rfl

@[simp, vcgen_simp] theorem JumpRel_label [Host] (p : Program) (s₀ : MachineData) (a : Int64) (l : Label)
    (s : MachineData) :
    JumpRel p s₀ a (.label l) s = (l ∈ Program.labels p ∧ a = label l ∧ SameStackFrame s₀ s) := by
  apply propext
  constructor
  · rintro (⟨l', hmem, hl, ha, hs⟩ | ⟨h, -⟩)
    · cases hl; exact ⟨hmem, ha, hs⟩
    · cases h
  · rintro ⟨hmem, ha, hs⟩
    exact Or.inl ⟨l, hmem, rfl, ha, hs⟩

@[simp, vcgen_simp] theorem JumpRel_exit [Host] (p : Program) (s₀ : MachineData) (a : Int64)
    (s : MachineData) :
    JumpRel p s₀ a .exit s = (a = s₀.retAddr.get! ∧ s.regs.get64 .rsp = s₀.regs.get64 .rsp + 8#64) := by
  apply propext
  constructor
  · rintro (⟨l', -, hl, -, -⟩ | ⟨-, ha, hs⟩)
    · cases hl
    · exact ⟨ha, hs⟩
  · rintro ⟨ha, hs⟩
    exact Or.inr ⟨rfl, ha, hs⟩

attribute [vcgen_simp] Program.labels_nil Program.labels_cons_instr Program.labels_cons_label
  MachineData.retAddr_eq

@[vcgen_simp] theorem Label.mem_cons (a b : Label) (l : List Label) : (a ∈ b :: l) = (a = b ∨ a ∈ l) :=
  propext List.mem_cons

@[vcgen_simp] theorem Label.mem_nil (a : Label) : (a ∈ ([] : List Label)) = False :=
  propext (iff_false_intro List.not_mem_nil)

/-- The control-flow rule as a spec: the abstract program is `cfgLoop` over the table of the text,
whose cells `ascend` fills block by block. The program is embedded in the host, so its labels are
distinct. -/
theorem refines_cfg {p : Program} [Embeds p] (tbl : Table CfgLabel (BlockM Aσ Unit))
    {s : MachineData} {ra : Int64}
    (h : ∀ blk ∈ Program.blocks p, ∀ t, SameStackFrame (s.push64 ra) t →
      ⦃(· = t)⦄ blk.body ⪯[Concretization.ofStateRepr abs] (Table.get tbl (CfgLabel.ofLabel blk.label))
        ⦃FallRel (s.push64 ra); JumpRel p (s.push64 ra)⦄) :
    ⦃(· = s.push64 ra)⦄ p ⪯[Concretization.ofStateRepr abs]
      (cfgLoop (Program.table p (Table.get tbl)) .entry) ⦃fun _ _ => ⊤; RetRel s ra⦄ :=
  ⟨wrp_cfg_le abs Program.labels_nodup_of_embeds h⟩

end

end Ascent.Kraken
