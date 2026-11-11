import Demo.Kraken
import Ascent.Table
import Ascent.BlockLoop
import Kraken.StateCfg
import Ascent.UB.StateT
import Ascent.UB.WhileLoop
import Ascent.Refinement.Lockstep

/-!
# Control-flow graphs

`Program.loop p r₀ cell` is the abstract program of a kraken text `p` with labels, for a function
whose frame has the stack pointer `r₀`. It runs the abstract cell of the entry block and then the
block loop of `Ascent.BlockLoop` over the table of the text. The table maps the address `label l`
of each label `l` to its cell followed by the fall through to the successor in the text. A block
program lives in `BlockM σ`, and a jump is the exception that carries its target address.

The loop dispatches in the manner of kraken's `Program.ContinueOnInternalExit`: a jump to the
address `a` runs the block at `a` while the stack pointer lies in the frame (`stayIn r₀`), and
leaves the loop with `a` otherwise. A return sets the stack pointer to `r₀ + 8` and leaves the loop
at the return address, whatever that address is. A jump inside the text assumes that the stack
pointer lies in the frame.

`refines_cfg` refines a text to that loop from one refinement per block. Both the blocks and the
text relate the concrete exit address to the abstract exception by equality (`AddrRel`).
-/

open Std.WP Lean.Order Ascent
open scoped Program.WP

attribute [vcgen_simp] Program.straight_nil Program.straight_cons_instr Program.straight_cons_label
  Program.straight_cons_byteArray

namespace Ascent.Kraken

abbrev BlockM (σ : Type) := ExceptT Int64 (StateT σ UB)

/-! ## The step shapes of a block program -/

namespace AInstr

section
variable {σ : Type}

noncomputable def modifyIf (g : σ → Prop) (f : σ → σ) : BlockM σ Unit :=
  fun st => UB.assume (g st) >>= fun _ => pure (.ok (), f st)

noncomputable def exitIf {α : Type} (g : σ → Prop) (f : σ → σ) (l : Int64) : BlockM σ α :=
  fun st => UB.assume (g st) >>= fun _ => pure (.error l, f st)

noncomputable def branch (s c : σ → Bool) (l : Int64) : BlockM σ Unit :=
  fun st => if c st then UB.assume (s st = true) >>= fun _ => pure (.error l, st) else pure (.ok (), st)

def peek {β : Type} (c : σ → β) : BlockM σ β :=
  fun st => pure (.ok (c st), st)

end

section
variable {σ : Type} (Qa : Unit → σ → Prop) (Ea : (Int64 → σ → Prop) × EStack⟨⟩) (st : σ)

theorem modifyIf_run (g f) : (modifyIf g f).run.run st = modifyIf g f st := rfl
theorem exitIf_run {α : Type} (g f l) : (exitIf g f l : BlockM σ α).run.run st = exitIf g f l st := rfl
theorem branch_run (s c l) : (branch s c l).run.run st = branch s c l st := rfl
theorem peek_run {β : Type} (c : σ → β) : (peek c).run.run st = peek c st := rfl

theorem wp_modifyIf (g f) :
    wp (modifyIf g f) Qa Ea st = (g st ∧ Qa () (f st)) := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, modifyIf_run]
  unfold modifyIf
  by_cases h : g st
  · rw [UB.assume_bind_of_pos h]
    simp only [UB.wp_pure_eq, h, true_and]
    rfl
  · rw [UB.assume_bind_of_neg h]
    simp only [UB.wp_fail_eq, bot_prop_eq, h, false_and]

theorem wp_exitIf {α : Type} {Qa : α → σ → Prop} (g f l) :
    wp (exitIf g f l : BlockM σ α) Qa Ea st = (g st ∧ Ea.1 l (f st)) := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, exitIf_run]
  unfold exitIf
  by_cases h : g st
  · rw [UB.assume_bind_of_pos h]
    simp only [UB.wp_pure_eq, h, true_and]
    rfl
  · rw [UB.assume_bind_of_neg h]
    simp only [UB.wp_fail_eq, bot_prop_eq, h, false_and]

theorem exitIf_bind {σ α β : Type} (g : σ → Prop) (f : σ → σ) (l : Int64)
    (k : α → BlockM σ β) : (exitIf g f l >>= k) = exitIf g f l := by
  apply ExceptT.ext
  apply StateT.ext
  intro st
  rw [ExceptT.run_bind, StateT.run_bind, exitIf_run, exitIf_run]
  unfold exitIf
  by_cases h : g st
  · rw [UB.assume_bind_of_pos h, UB.assume_bind_of_pos h]
    rfl
  · rw [UB.assume_bind_of_neg h, UB.assume_bind_of_neg h]
    rfl

theorem wp_peek {β : Type} {Qb : β → σ → Prop} (c : σ → β) :
    wp (peek c) Qb Ea st = Qb (c st) st := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, peek_run]
  simp only [peek, UB.wp_pure_eq]
  rfl

theorem wp_branch (s c l) :
    wp (branch s c l) Qa Ea st = if c st then s st = true ∧ Ea.1 l st else Qa () st := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, branch_run]
  unfold branch
  split
  · by_cases h : s st = true
    · rw [UB.assume_bind_of_pos h]
      simp only [UB.wp_pure_eq, h, true_and]
      rfl
    · rw [UB.assume_bind_of_neg h]
      simp [UB.wp_fail_eq, bot_prop_eq, h]
  · simp only [UB.wp_pure_eq, *]
    rfl

end

end AInstr

/-! ## The stack test and the table of a text -/

/-- The stack pointer `p` lies at or below `r₀`, in kraken's serial order. -/
def stayAt (r₀ p : BitVec 64) : Bool := !(BitVec.slt 0#64 (p - r₀))

@[simp, grind =] theorem stayAt_self (r : BitVec 64) : stayAt r r = true := by
  simp [stayAt]

def stayIn (r₀ : BitVec 64) (st : MachineData) : Bool := stayAt r₀ (st.regs.get64 .rsp)

theorem stayIn_iff (s₀ st : MachineData) :
    stayIn (s₀.regs.get64 .rsp) st = true ↔ st.StackAtOrBelow s₀ := by
  simp only [stayIn, stayAt, Bool.not_eq_eq_eq_not, Bool.not_true, MachineData.StackAtOrBelow,
    MachineData.StackBelow, BitVec.SerialLt, BitVec.slt, decide_eq_false_iff_not]
  simp

@[simp, vcgen_simp] theorem stayIn_setReg_rsp (r₀ v : BitVec 64) (st : MachineData) :
    stayIn r₀ { st with regs := st.regs.set64 .rsp v } = !(BitVec.slt 0#64 (v - r₀)) := by
  simp [stayIn, stayAt]

noncomputable def jumpTo [Host] {σ : Type} (s : σ → Bool) : Option Label → BlockM σ Unit
  | none => pure ()
  | some l => AInstr.branch s (fun _ => true) (label l)

@[vcgen_simp] theorem jumpTo_none [Host] {σ : Type} (s : σ → Bool) :
    (jumpTo s none : BlockM σ Unit) = pure () := rfl
@[vcgen_simp] theorem jumpTo_some [Host] {σ : Type} (s : σ → Bool) (l : Label) :
    (jumpTo s (some l) : BlockM σ Unit) = AInstr.branch s (fun _ => true) (label l) := rfl

/-- The table of a text: the address of each label maps to the cell of the label followed by the
fall through to its successor. A later label comes first, so that of two labels at one address
the later one runs. -/
noncomputable def Program.table [Host] (p : Program) (r₀ : BitVec 64) (cell : Option Label → BlockM MachineData Unit) :
    Table Int64 (BlockM MachineData Unit) :=
  ((Program.blocks p).filterMap fun blk =>
    blk.label.map fun l => (label l, cell blk.label >>= fun _ => jumpTo (stayIn r₀) blk.next)).reverse

def Program.entryNext (p : Program) : Option Label := Program.firstLabel (Program.view p).2

noncomputable def Program.loop [Host] (p : Program) (r₀ : BitVec 64) (cell : Option Label → BlockM MachineData Unit) :
    BlockM MachineData Unit :=
  tryCatch (cell none >>= fun _ => jumpTo (stayIn r₀) (Program.entryNext p))
    (cfgLoop (stayIn r₀) (Program.table p r₀ cell))

/-! ## Separated labels

A text is separated if every label is followed by an instruction that is not padding. Then two
distinct labels have distinct addresses (`Host.label_ne`). -/

def Instr.isPadding : Instr → Bool
  | .regular _ _ (.nop _) => true
  | .regular _ _ (.nopalign _ _) => true
  | _ => false

theorem Instr.not_isPadding {i : Instr} (h : Instr.isPadding i = false) : ¬ i.IsPadding := by
  intro hp
  cases hp <;> simp [Instr.isPadding] at h

def Program.Separated : Program → Bool
  | [] => true
  | .label _ :: rest =>
    (match rest with
      | .instr i :: _ => !Instr.isPadding i
      | _ => false) && Program.Separated rest
  | _ :: rest => Program.Separated rest

theorem Program.Separated.next : ∀ {p : Program} {i : Nat} {l : Label}, Program.Separated p = true →
    p[i]? = some (.label l) → ∃ ins, p[i + 1]? = some (.instr ins) ∧ ¬ ins.IsPadding
  | [], _, _, _, h => nomatch h
  | .label l' :: rest, 0, l, hs, _ => by
    simp only [Program.Separated, Bool.and_eq_true] at hs
    obtain ⟨hm, -⟩ := hs
    split at hm
    · exact ⟨_, rfl, Instr.not_isPadding (by simpa using hm)⟩
    · exact nomatch hm
  | .label l' :: rest, i + 1, l, hs, h => by
    simp only [Program.Separated, Bool.and_eq_true] at hs
    exact Program.Separated.next (p := rest) hs.2 h
  | .instr _ :: rest, 0, _, _, h => nomatch h
  | .instr _ :: rest, i + 1, _, hs, h => Program.Separated.next (p := rest) hs h
  | .byteArray _ :: rest, 0, _, _, h => nomatch h
  | .byteArray _ :: rest, i + 1, _, hs, h => Program.Separated.next (p := rest) hs h

theorem Program.label_ne_of_separated [Host] {p : Program} [hp : Embeds p]
    (hs : Program.Separated p = true) {l l' : Label} (hl : l ∈ Program.labels p)
    (hl' : l' ∈ Program.labels p) (hne : l ≠ l') : label l ≠ label l' := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (Program.mem_labels.mp hl)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (Program.mem_labels.mp hl')
  have hH := hp.embedding.isInfixAt
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · obtain ⟨ins, hi1, hpad⟩ := Program.Separated.next hs hi
    exact Host.label_ne i j hH h hi hi1 hj hpad
  · rw [hi] at hj
    cases hj
    exact absurd rfl hne
  · obtain ⟨ins, hj1, hpad⟩ := Program.Separated.next hs hj
    exact (Host.label_ne j i hH h hj hj1 hi hpad).symm

theorem Program.label_inj_of_separated [Host] {p : Program} [Embeds p]
    (hs : Program.Separated p = true) {l l' : Label} (hl : l ∈ Program.labels p)
    (hl' : l' ∈ Program.labels p) (h : label l = label l') : l = l' :=
  Classical.byContradiction fun hne => Program.label_ne_of_separated hs hl hl' hne h

/-! ## Lookup in the table -/

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

theorem Program.block_unique_blocksFrom {b : Option Label} :
    ∀ {j : Nat} {body : Program} {bs : List (Label × Program)}, (bs.map (·.1)).Nodup →
      (∀ lb ∈ bs, b ≠ some lb.1) → ∀ {blk blk' : Program.Block},
        blk ∈ Program.blocksFrom b j body bs → blk' ∈ Program.blocksFrom b j body bs →
        blk.label = blk'.label → blk = blk'
  | _, _, [], _, _, blk, blk', h, h', _ => by
    simp only [Program.blocksFrom, List.mem_singleton] at h h'
    rw [h, h']
  | j, body, (l, body') :: bs, hnd, hb, blk, blk', h, h', he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hb' : ∀ lb ∈ bs, some l ≠ some lb.1 :=
      fun lb hlb heq => hnd.1 ⟨lb, hlb, (Option.some.inj heq).symm⟩
    have hne : ∀ {x : Program.Block}, x ∈ Program.blocksFrom (some l) (j + 1) body' bs → x.label ≠ b := by
      intro x hx
      rcases Program.label_mem_blocksFrom hx with h | ⟨lb, hlb, h⟩
      · rw [h]; exact (hb (l, body') List.mem_cons_self).symm
      · rw [h]; exact (hb lb (List.mem_cons_of_mem _ hlb)).symm
    simp only [Program.blocksFrom, List.mem_cons] at h h'
    rcases h with rfl | h <;> rcases h' with rfl | h'
    · rfl
    · exact absurd he.symm (hne h')
    · exact absurd he (hne h)
    · exact Program.block_unique_blocksFrom hnd.2 hb' h h' he

theorem Program.block_unique {p : Program} (hnd : (Program.labels p).Nodup) {blk blk' : Program.Block}
    (h : blk ∈ Program.blocks p) (h' : blk' ∈ Program.blocks p) (he : blk.label = blk'.label) :
    blk = blk' := by
  rw [Program.labels_view] at hnd
  exact Program.block_unique_blocksFrom hnd (fun _ _ => by simp) h h' he

theorem Program.label_mem_labels {p : Program} {blk : Program.Block} {l : Label}
    (h : blk ∈ Program.blocks p) (hl : blk.label = some l) : l ∈ Program.labels p := by
  rw [Program.labels_view]
  rcases Program.label_mem_blocksFrom h with h' | ⟨lb, hlb, h'⟩
  · rw [hl] at h'; cases h'
  · rw [hl] at h'
    cases h'
    exact List.mem_map_of_mem hlb

theorem Program.exists_block_of_mem_labels {p : Program} {l : Label} (h : l ∈ Program.labels p) :
    ∃ blk ∈ Program.blocks p, blk.label = some l := by
  rw [Program.labels_view] at h
  obtain ⟨⟨l, body⟩, hlb, rfl⟩ := List.mem_map.mp h
  unfold Program.blocks
  generalize (Program.view p).1 = b0 at *
  generalize (Program.view p).2 = bs at hlb
  suffices ∀ (b : Option Label) j body0, ∃ blk ∈ Program.blocksFrom b j body0 bs, blk.label = some l from
    this none 0 b0
  induction bs with
  | nil => exact nomatch hlb
  | cons lb bs ih =>
    intro b j body0
    rcases List.mem_cons.mp hlb with rfl | hlb
    · cases bs with
      | nil => exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩
      | cons _ _ => exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
    · obtain ⟨blk, hblk, hl⟩ := ih hlb (some lb.1) (j + 1) lb.2
      exact ⟨blk, List.mem_cons_of_mem _ hblk, hl⟩

theorem List.lookup_mem {κ β : Type} [DecidableEq κ] :
    ∀ {L : List (κ × β)} {k : κ} {b : β}, L.lookup k = some b → (k, b) ∈ L
  | [], _, _, h => nomatch h
  | (k', b') :: L, k, b, h => by
    simp only [List.lookup] at h
    split at h
    · next he =>
      cases h
      simp only [beq_iff_eq] at he
      rw [he]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.lookup_mem h)

theorem List.lookup_of_mem {κ β : Type} [DecidableEq κ] :
    ∀ {L : List (κ × β)} {k : κ} {b : β}, (k, b) ∈ L → (∀ b', (k, b') ∈ L → b' = b) →
      L.lookup k = some b
  | [], _, _, h, _ => nomatch h
  | (k', b') :: L, k, b, h, hu => by
    simp only [List.lookup]
    split
    · next he =>
      simp only [beq_iff_eq] at he
      rw [hu b' (by rw [he]; exact List.mem_cons_self)]
    · next he =>
      rcases List.mem_cons.mp h with h | h
      · cases h; simp at he
      · exact List.lookup_of_mem h fun b'' h'' => hu b'' (List.mem_cons_of_mem _ h'')

theorem List.lookup_eq_none {κ β : Type} [DecidableEq κ] :
    ∀ {L : List (κ × β)} {k : κ}, L.lookup k = none → ∀ b, (k, b) ∉ L
  | [], _, _, _, h => nomatch h
  | (k', b') :: L, k, h, b, hm => by
    simp only [List.lookup] at h
    split at h
    · exact nomatch h
    · next he =>
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm; simp at he
      · exact List.lookup_eq_none h b hm

section
variable [Host] {p : Program} {r₀ : BitVec 64} {cell : Option Label → BlockM MachineData Unit}

theorem Program.mem_table {a : Int64} {b : BlockM MachineData Unit} :
    (a, b) ∈ Program.table p r₀ cell ↔ ∃ blk ∈ Program.blocks p, ∃ l, blk.label = some l ∧
      label l = a ∧ b = (cell blk.label >>= fun _ => jumpTo (stayIn r₀) blk.next) := by
  simp only [Program.table, List.mem_reverse, List.mem_filterMap, Option.map_eq_some_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨blk, hblk, l, hl, ha, hb⟩
    exact ⟨blk, hblk, l, hl, ha, hb.symm⟩
  · rintro ⟨blk, hblk, l, hl, ha, hb⟩
    exact ⟨blk, hblk, l, hl, ha, hb.symm⟩

theorem Program.table_get?_label [Embeds p] (hs : Program.Separated p = true) {blk : Program.Block}
    {l : Label} (hblk : blk ∈ Program.blocks p) (hl : blk.label = some l) :
    (Program.table p r₀ cell).get? (label l)
      = some (cell blk.label >>= fun _ => jumpTo (stayIn r₀) blk.next) := by
  refine List.lookup_of_mem (Program.mem_table.mpr ⟨blk, hblk, l, hl, rfl, rfl⟩) fun b' hb' => ?_
  obtain ⟨blk', hblk', l', hl', ha, rfl⟩ := Program.mem_table.mp hb'
  have hll : l' = l := Program.label_inj_of_separated hs (Program.label_mem_labels hblk' hl')
    (Program.label_mem_labels hblk hl) ha
  subst hll
  rw [Program.block_unique Program.labels_nodup_of_embeds hblk' hblk (hl'.trans hl.symm)]

theorem Program.table_get?_some {a : Int64} {b : BlockM MachineData Unit}
    (h : (Program.table p r₀ cell).get? a = some b) :
    ∃ blk ∈ Program.blocks p, ∃ l, blk.label = some l ∧ label l = a ∧
      b = (cell blk.label >>= fun _ => jumpTo (stayIn r₀) blk.next) :=
  Program.mem_table.mp (List.lookup_mem h)

theorem Program.table_get?_none {a : Int64} (h : (Program.table p r₀ cell).get? a = none)
    {l : Label} (hl : l ∈ Program.labels p) : label l ≠ a := by
  rintro rfl
  obtain ⟨blk, hblk, hbl⟩ := Program.exists_block_of_mem_labels hl
  exact List.lookup_eq_none h _ (Program.mem_table.mpr ⟨blk, hblk, l, hbl, rfl, rfl⟩)

end

/-! ## The run of a block program -/

theorem wp_BlockM_eq {σ α : Type} (x : BlockM σ α) (Qa : α → σ → Prop)
    (Ea : (Int64 → σ → Prop) × EStack⟨⟩) (st : σ) :
    wp x Qa Ea st = match x.run.run st with
      | none => False
      | some (.ok a, st') => Qa a st'
      | some (.error e, st') => Ea.1 e st' := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq]
  rcases x.run.run st with _ | ⟨l' | a, st'⟩
  · exact bot_prop_eq
  · rfl
  · rfl

theorem BlockM.run_bind {σ α β : Type} (x : BlockM σ α) (k : α → BlockM σ β) (st : σ) :
    (x >>= k).run.run st = (x.run.run st >>= fun p =>
      match p.1 with
      | .ok a => (k a).run.run p.2
      | .error e => pure (.error e, p.2)) := by
  rw [ExceptT.run_bind, StateT.run_bind]
  congr 1
  funext p
  rcases p with ⟨_ | _, _⟩ <;> rfl

theorem UB.some_bind {α β : Type} (a : α) (f : α → UB β) : (Bind.bind (m := UB) (some a) f) = f a := rfl
theorem UB.map_some {α β : Type} (g : α → β) (a : α) :
    (Functor.map (f := UB) g (some a)) = some (g a) := rfl
theorem UB.pure_eq {α : Type} (a : α) : (pure a : UB α) = some a := rfl
theorem UB.fail_eq {α : Type} : (UB.fail : UB α) = none := rfl
theorem UB.bind_eq_some {α β : Type} (x : UB α) (f : α → UB β) (b : β) :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b := Option.bind_eq_some_iff
theorem UB.map_eq_some {α β : Type} (g : α → β) (x : UB α) (b : β) :
    (g <$> x) = some b ↔ ∃ a, x = some a ∧ g a = b := Option.map_eq_some_iff

theorem wp_throw_block {σ α : Type} (l : Int64) (Q : α → σ → Prop) (E : (Int64 → σ → Prop) × EStack⟨⟩)
    (s : σ) : wp (throw l : BlockM σ α) Q E s = E.1 l s :=
  BlockLoop.wp_throw l Q E s

theorem wp_tryCatch_block {σ α : Type} (x : BlockM σ α) (h : Int64 → BlockM σ α) (Q : α → σ → Prop)
    (E : (Int64 → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (tryCatch x h) Q E s = wp x Q (fun l => wp (h l) Q E, E.2) s :=
  BlockLoop.wp_tryCatch x h Q E s

theorem wp_get {σ : Type} (Q : σ → σ → Prop) (E : (Int64 → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (get : BlockM σ σ) Q E s = Q s s := by
  rw [wp_BlockM_eq]
  rfl

theorem wp_get_bind {σ α : Type} (k : σ → BlockM σ α) (Q : α → σ → Prop)
    (E : (Int64 → σ → Prop) × EStack⟨⟩) (s : σ) : wp (get >>= k) Q E s = wp (k s) Q E s := by
  rw [wp_BlockM_eq, wp_BlockM_eq]
  rfl

/-! ## The exit relation -/

/-- The concrete exit address equals the abstract exception. The stack pointer `r₀` and the return
address `ra` of the entry state name the frame for the rules of a step. -/
def AddrRel (_r₀ : BitVec 64) (_ra : Int64) : Int64 → Int64 → MachineData → Prop := fun a a' _ => a = a'

@[simp, grind =] theorem AddrRel_eq (r₀ : BitVec 64) (ra : Int64) (a a' : Int64) (s : MachineData) :
    AddrRel r₀ ra a a' s = (a = a') := rfl

noncomputable instance {Aσ : Type} :
    EPostsConcretization (MachineData → Prop) (Aσ → Prop) (Int64 → MachineData → Prop)
      ((Int64 → Aσ → Prop) × EStack⟨⟩) (Int64 → Int64 → MachineData → Prop) where
  ePosts γ E Ea := γ.post E Ea.1

@[simp, grind norm] theorem ePosts_ret {Aσ : Type} (γ : Concretization (MachineData → Prop) (Aσ → Prop))
    (E : Int64 → Int64 → MachineData → Prop) (Ea : (Int64 → Aσ → Prop) × EStack⟨⟩) :
    EPostsConcretization.ePosts (CEPosts := Int64 → MachineData → Prop) γ E Ea = γ.post E Ea.1 := rfl

/-! ## The control-flow rule -/

section
variable [Host] [FunDecls] (abs : MachineData → MachineData)
  (habs : ∀ s, (abs s).regs = s.regs)
include habs

theorem wrp_cfg_le {p : Program} [Embeds p] (hs : Program.Separated p = true)
    {cell : Option Label → BlockM MachineData Unit} {s₀ : MachineData} {ra : Int64}
    (h : ∀ blk ∈ Program.blocks p, ∀ t,
      ⦃(· = t)⦄ blk.body ⪯[Concretization.ofStateRepr abs] (cell blk.label)
        ⦃fun _ _ _ => True; AddrRel (s₀.regs.get64 .rsp) ra⦄) :
    (fun t => t = s₀) ⊑ wrp (Concretization.ofStateRepr abs) p
      (Program.loop p (s₀.regs.get64 .rsp) cell) (fun _ _ => ⊤) (AddrRel (s₀.regs.get64 .rsp) ra) := by
  have hstay : ∀ t, stayIn (s₀.regs.get64 .rsp) (abs t) = true ↔ t.StackAtOrBelow s₀ := by
    intro t
    rw [stayIn_iff]
    simp only [MachineData.StackAtOrBelow, MachineData.StackBelow, habs]
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred] at ht
  obtain ⟨rfl, hpre⟩ := ht
  let r₀ := t.regs.get64 .rsp
  let st := stayIn r₀
  let T := Program.table p r₀ cell
  let H : (Int64 → MachineData → Prop) × EStack⟨⟩ := (fun a => wp (cfgLoop st T a) Qa Ea, Ea.2)
  let I : Program.CfgInvariant := fun {_} l u =>
    st (abs u) = true ∧ wp (cfgLoop st T (label l)) Qa Ea (abs u)
  let Q : Unit → MachineData → Prop := fun _ u =>
    (Concretization.ofStateRepr abs).post (fun _ _ => ⊤) Qa () u
  let var : Program.CfgVariant := fun l u => steps st T (label l) (abs u)
  have hentry : (Program.blocks p).head? = some ⟨none, 0, Program.straight (Program.view p).1,
      Program.entryNext p⟩ := by
    unfold Program.blocks Program.entryNext
    cases (Program.view p).2 <;> rfl
  refine Program.WP.cfg (p := p) (Q := Q)
    (E := EPostsConcretization.ePosts (Concretization.ofStateRepr abs) (AddrRel (t.regs.get64 .rsp) ra) Ea)
    (s₀ := t) @I var ?_
  intro blk hmem u hI
  have hrun : wp (cell blk.label >>= fun _ => jumpTo st blk.next) Qa H (abs u)
      ∧ ∀ l, blk.label = some l → st (abs u) = true ∧
        T.get? (label l) = some (cell blk.label >>= fun _ => jumpTo st blk.next) ∧
        ∃ r, cfgFix st T (label l) (abs u) = some r := by
    cases hl : blk.label with
    | none =>
      rw [hl] at hI
      change u = t at hI
      subst hI
      have hblk : blk = ⟨none, 0, Program.straight (Program.view p).1, Program.entryNext p⟩ := by
        refine Program.block_unique Program.labels_nodup_of_embeds hmem ?_ hl
        exact List.mem_of_mem_head? hentry
      rw [hblk]
      refine ⟨?_, fun _ h => nomatch h⟩
      simpa only [Program.loop, BlockLoop.wp_tryCatch] using hpre
    | some l =>
      rw [hl] at hI
      obtain ⟨hst, hw⟩ := hI
      have hTb := Program.table_get?_label (r₀ := r₀) (cell := cell) hs hmem hl
      have hfix : ∃ r, cfgFix st T (label l) (abs u) = some r := by
        rw [wp_BlockM_eq, cfgLoop_run] at hw
        revert hw
        cases cfgFix st T (label l) (abs u) <;> intro hw
        · exact hw.elim
        · exact ⟨_, rfl⟩
      rw [wp_cfgLoop_some st T Qa Ea hTb hst] at hw
      rw [hl] at hTb hw
      refine ⟨hw, fun l' hl' => ?_⟩
      cases hl'
      exact ⟨hst, hTb, hfix⟩
  obtain ⟨hw, hblk⟩ := hrun
  let c := cell blk.label
  have hdec : ∀ a v, (c >>= fun _ => jumpTo st blk.next).run.run (abs u) = some (.error a, abs v) →
      ∀ l, blk.label = some l → steps st T a (abs v) < steps st T (label l) (abs u) := by
    intro a v hr l hl
    obtain ⟨hst, hTb, r, hfix⟩ := hblk l hl
    exact steps_lt st T hTb hst hr hfix
  rw [WPMonadExact.wp_bind_eq, wp_BlockM_eq] at hw
  let Qa' : Unit → MachineData → Prop := fun _ st' =>
    wp (jumpTo st blk.next : BlockM MachineData Unit) Qa H st' ∧ c.run.run (abs u) = some (.ok (), st')
  let Ea' : (Int64 → MachineData → Prop) × EStack⟨⟩ :=
    (fun a st' => wp (cfgLoop st T a) Qa Ea st' ∧ c.run.run (abs u) = some (.error a, st'), Ea.2)
  have hpre' : wp c Qa' Ea' (abs u) := by
    rw [wp_BlockM_eq]
    revert hw
    rcases hc : c.run.run (abs u) with _ | ⟨a | _, st'⟩ <;> intro hw
    · exact hw.elim
    · exact ⟨hw, hc⟩
    · exact ⟨hw, hc⟩
  have hb := wrp_transport (h blk hmem u).le_wrp Qa' Ea'
  have hmeet : ((fun t' => t' = u) ⊓ (Concretization.ofStateRepr abs).pred (wp c Qa' Ea')) u := by
    simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]
    exact ⟨trivial, hpre'⟩
  have hwp := hb u hmeet
  have hjump : ∀ v a, wp (cfgLoop st T a) Qa Ea (abs v) →
      (∀ l, blk.label = some l → steps st T a (abs v) < steps st T (label l) (abs u)) →
      Program.Intercept (Program.labels p) t
        (fun l j s' => I (s₀ := t) l s' ∧ Program.Decreases var blk.label blk.idx u l j s')
        (EPostsConcretization.ePosts (Concretization.ofStateRepr abs) (AddrRel (t.regs.get64 .rsp) ra) Ea) a v := by
    intro v a hE hd
    cases hsv : st (abs v) with
    | false =>
      rw [wp_cfgLoop_leave st T Qa Ea hsv] at hE
      refine Program.Intercept.intro (Or.inr ⟨?_, fun _ _ _ => ?_⟩)
      · show (Concretization.ofStateRepr abs).post (AddrRel (t.regs.get64 .rsp) ra) Ea.1 a v
        simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
          meet_prop_eq_and, Concretization.ofStateRepr_pred, AddrRel]
        exact ⟨a, rfl, hE⟩
      · have h1 : ¬ v.StackAtOrBelow t := fun h2 => by
          have := (hstay v).mpr h2
          simp only [st, r₀] at hsv
          rw [hsv] at this
          exact nomatch this
        simpa only [MachineData.StackAtOrBelow, Classical.not_not] using h1
    | true =>
    cases hT : T.get? a with
    | none =>
      rw [wp_cfgLoop_none st T Qa Ea hT] at hE
      refine Program.Intercept.intro (Or.inr ⟨?_, fun l hl ha => ?_⟩)
      · show (Concretization.ofStateRepr abs).post (AddrRel (t.regs.get64 .rsp) ra) Ea.1 a v
        simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
          meet_prop_eq_and, Concretization.ofStateRepr_pred, AddrRel]
        exact ⟨a, rfl, hE⟩
      · exact absurd ha (Program.table_get?_none hT hl)
    | some b =>
      obtain ⟨blk', hblk', l, hl, ha, -⟩ := Program.table_get?_some hT
      subst ha
      refine Program.Intercept.intro (Or.inl ⟨(hstay v).mp hsv, l, rfl,
        Program.label_mem_labels hblk' hl, ⟨⟨hsv, hE⟩, ?_⟩⟩)
      cases hbl : blk.label with
      | none => trivial
      | some l₀ => exact Or.inl (hd l₀ hbl)
  refine Program.wp_mono (fun u' hu => ?_) (fun u' hu => ?_) hwp
  · change (Concretization.ofStateRepr abs).post (fun _ _ _ => True) Qa' () u'.data at hu
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
      meet_prop_eq_and, Concretization.ofStateRepr_pred] at hu
    obtain ⟨-, -, hQ, hc⟩ := hu
    show Program.Next @I t Q (Program.Decreases var blk.label blk.idx u) blk.next (blk.idx + 1) u'.data
    cases hn : blk.next with
    | none =>
      rw [hn, jumpTo_none, WPMonadExact.wp_pure_eq] at hQ
      simp only [Program.Next, Q, Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, top_apply, top_prop_eq, Concretization.ofStateRepr_pred]
      exact ⟨(), trivial, hQ⟩
    | some l' =>
      rw [hn, jumpTo_some, AInstr.wp_branch] at hQ
      simp only [↓reduceIte] at hQ
      obtain ⟨hsu, hQ⟩ := hQ
      refine ⟨⟨hsu, hQ⟩, ?_⟩
      cases hbl : blk.label with
      | none => trivial
      | some l₀ =>
        refine Or.inl (hdec (label l') u'.data ?_ l₀ hbl)
        rw [BlockM.run_bind, hc, hn]
        show (AInstr.branch st (fun _ => true) (label l')).run.run (abs u'.data) = _
        rw [AInstr.branch_run]
        simp only [AInstr.branch, ↓reduceIte, UB.assume_bind_of_pos hsu]
        rfl
  · change (Concretization.ofStateRepr abs).post (AddrRel (t.regs.get64 .rsp) ra) Ea'.1 u'.pc u'.data at hu
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
      meet_prop_eq_and, Concretization.ofStateRepr_pred, AddrRel] at hu
    obtain ⟨a', rfl, hE, hc⟩ := hu
    refine hjump u'.data u'.pc hE fun l hl => hdec u'.pc u'.data ?_ l hl
    rw [BlockM.run_bind, hc]
    rfl

/-- The control-flow rule as a spec: the abstract program is the block loop over the table of the
text, whose cells `ascend` fills block by block. -/
theorem refines_cfg {p : Program} [Embeds p] {r₀ : BitVec 64} {ra : Int64}
    (tbl : Table (Option Label) (BlockM MachineData Unit)) (hs : Program.Separated p = true := by decide +kernel)
    (h : ∀ blk ∈ Program.blocks p, ∀ t,
      ⦃(· = t)⦄ blk.body ⪯[Concretization.ofStateRepr abs] (Table.get tbl blk.label)
        ⦃fun _ _ _ => True; AddrRel r₀ ra⦄) :
    ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ p ⪯[Concretization.ofStateRepr abs]
      (Program.loop p r₀ (Table.get tbl)) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄ :=
  ⟨fun t ⟨hrt, _⟩ => by
    subst hrt
    exact wrp_cfg_le abs habs hs (s₀ := t) h t rfl⟩

end

end Ascent.Kraken
