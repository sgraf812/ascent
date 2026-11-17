import Demo.Kraken
import Distillery.Table
import Distillery.BlockLoop
import Demo.Kraken.WP
import Demo.CfgGhost
import Distillery.Demonic.StateT
import Distillery.Demonic.WhileLoop
import Distillery.Refinement.Lockstep

/-!
# Control-flow graphs

`Program.loop p r₀ cell` is the abstract program of a kraken text `p` with labels, for a function
whose frame has the stack pointer `r₀`. It runs the abstract cell of the entry block and then the
block loop of `Distillery.BlockLoop` over the table of the text. The table maps the address `label l`
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

open Std.WP Lean.Order Distillery
open scoped Program.WP

attribute [vcgen_simp] Program.straight_nil Program.straight_cons_instr Program.straight_cons_label
  Program.straight_cons_byteArray

namespace Distillery.Kraken

abbrev BlockM (σ : Type) := ExceptT Int64 (StateT σ Demonic)

/-! ## The step shapes of a block program -/

namespace AInstr

section
variable {σ : Type}

noncomputable def modifyIf (g : σ → Prop) (f : σ → σ) : BlockM σ Unit :=
  fun st => Demonic.assert (g st) >>= fun _ => pure (.ok (), f st)

noncomputable def exitIf {α : Type} (g : σ → Prop) (f : σ → σ) (l : Int64) : BlockM σ α :=
  fun st => Demonic.assert (g st) >>= fun _ => pure (.error l, f st)

noncomputable def branch (s c : σ → Bool) (l : Int64) : BlockM σ Unit :=
  fun st => if c st then Demonic.assert (s st = true) >>= fun _ => pure (.error l, st) else pure (.ok (), st)

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
  · rw [Demonic.assert_bind_of_pos h]
    simp only [Demonic.wp_pure_eq, h, true_and]
    rfl
  · rw [Demonic.assert_bind_of_neg h]
    simp only [Demonic.wp_fail_eq, bot_prop_eq, h, false_and]

theorem wp_exitIf {α : Type} {Qa : α → σ → Prop} (g f l) :
    wp (exitIf g f l : BlockM σ α) Qa Ea st = (g st ∧ Ea.1 l (f st)) := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, exitIf_run]
  unfold exitIf
  by_cases h : g st
  · rw [Demonic.assert_bind_of_pos h]
    simp only [Demonic.wp_pure_eq, h, true_and]
    rfl
  · rw [Demonic.assert_bind_of_neg h]
    simp only [Demonic.wp_fail_eq, bot_prop_eq, h, false_and]

theorem exitIf_bind {σ α β : Type} (g : σ → Prop) (f : σ → σ) (l : Int64)
    (k : α → BlockM σ β) : (exitIf g f l >>= k) = exitIf g f l := by
  apply ExceptT.ext
  apply StateT.ext
  intro st
  rw [ExceptT.run_bind, StateT.run_bind, exitIf_run, exitIf_run]
  unfold exitIf
  by_cases h : g st
  · rw [Demonic.assert_bind_of_pos h, Demonic.assert_bind_of_pos h]
    rfl
  · rw [Demonic.assert_bind_of_neg h, Demonic.assert_bind_of_neg h]
    rfl

theorem wp_peek {β : Type} {Qb : β → σ → Prop} (c : σ → β) :
    wp (peek c) Qb Ea st = Qb (c st) st := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, peek_run]
  simp only [peek, Demonic.wp_pure_eq]
  rfl

theorem wp_branch (s c l) :
    wp (branch s c l) Qa Ea st = if c st then s st = true ∧ Ea.1 l st else Qa () st := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, branch_run]
  unfold branch
  split
  · by_cases h : s st = true
    · rw [Demonic.assert_bind_of_pos h]
      simp only [Demonic.wp_pure_eq, h, true_and]
      rfl
    · rw [Demonic.assert_bind_of_neg h]
      simp [Demonic.wp_fail_eq, bot_prop_eq, h]
  · simp only [Demonic.wp_pure_eq, *]
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
  simp only [stayIn, stayAt, Bool.not_eq_eq_eq_not, Bool.not_true, MachineData.stackAtOrBelow_def,
    MachineData.stackBelow_def, BitVec.serialLt_def, BitVec.slt, decide_eq_false_iff_not]
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
    simp only [Program.blocksFrom_nil, List.mem_singleton] at h
    subst h
    exact Or.inl rfl
  | j, body, (l, body') :: bs, blk, h => by
    simp only [Program.blocksFrom_cons, List.mem_cons] at h
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
    simp only [Program.blocksFrom_nil, List.mem_singleton] at h h'
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
    simp only [Program.blocksFrom_cons, List.mem_cons] at h h'
    rcases h with rfl | h <;> rcases h' with rfl | h'
    · rfl
    · exact absurd he.symm (hne h')
    · exact absurd he (hne h)
    · exact Program.block_unique_blocksFrom hnd.2 hb' h h' he

theorem Program.block_unique {p : Program} (hnd : (Program.labels p).Nodup) {blk blk' : Program.Block}
    (h : blk ∈ Program.blocks p) (h' : blk' ∈ Program.blocks p) (he : blk.label = blk'.label) :
    blk = blk' := by
  rw [Program.labels_view] at hnd
  rw [Program.blocks_eq] at h h'
  exact Program.block_unique_blocksFrom hnd (fun _ _ => by simp) h h' he

theorem Program.label_mem_labels {p : Program} {blk : Program.Block} {l : Label}
    (h : blk ∈ Program.blocks p) (hl : blk.label = some l) : l ∈ Program.labels p := by
  rw [Program.labels_view]
  rw [Program.blocks_eq] at h
  rcases Program.label_mem_blocksFrom h with h' | ⟨lb, hlb, h'⟩
  · rw [hl] at h'; cases h'
  · rw [hl] at h'
    cases h'
    exact List.mem_map_of_mem hlb

theorem Program.exists_block_of_mem_labels {p : Program} {l : Label} (h : l ∈ Program.labels p) :
    ∃ blk ∈ Program.blocks p, blk.label = some l := by
  rw [Program.labels_view] at h
  obtain ⟨⟨l, body⟩, hlb, rfl⟩ := List.mem_map.mp h
  rw [Program.blocks_eq]
  generalize (Program.view p).1 = b0 at *
  generalize (Program.view p).2 = bs at hlb
  suffices ∀ (b : Option Label) j body0, ∃ blk ∈ Program.blocksFrom b j body0 bs, blk.label = some l from
    this none 0 b0
  induction bs with
  | nil => exact nomatch hlb
  | cons lb bs ih =>
    obtain ⟨l₁, b₁⟩ := lb
    intro b j body0
    rw [Program.blocksFrom_cons]
    rcases List.mem_cons.mp hlb with heq | hlb
    · cases heq
      cases bs with
      | nil => exact ⟨_, List.mem_cons_of_mem _ (by rw [Program.blocksFrom_nil]; exact List.mem_singleton_self _), rfl⟩
      | cons lb' _ =>
        obtain ⟨_, _⟩ := lb'
        exact ⟨_, List.mem_cons_of_mem _ (by rw [Program.blocksFrom_cons]; exact List.mem_cons_self), rfl⟩
    · obtain ⟨blk, hblk, hl⟩ := ih hlb (some l₁) (j + 1) b₁
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
    wp x Qa Ea st = (x.run.run st).wpD (BlockLoop.runPost Qa Ea) :=
  BlockLoop.wp_run_eq x Qa Ea st

theorem BlockM.run_bind {σ α β : Type} (x : BlockM σ α) (k : α → BlockM σ β) (st : σ) :
    (x >>= k).run.run st = (x.run.run st >>= fun p =>
      match p.1 with
      | .ok a => (k a).run.run p.2
      | .error e => pure (.error e, p.2)) := by
  rw [ExceptT.run_bind, StateT.run_bind]
  congr 1
  funext p
  rcases p with ⟨_ | _, _⟩ <;> rfl

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

/-- The exit relation of a block of the text `p` in the frame `r₀`: a jump that stays in the frame
goes to a label of `p` at the same address, and every other exit satisfies the exit relation `E` of
the function. -/
def BlockExit [Host] (p : Program) (r₀ : BitVec 64) (E : Int64 → Int64 → MachineData → Prop) :
    Int64 → Int64 → MachineData → Prop :=
  fun c l t => (stayIn r₀ t = true ∧ c = l ∧ ∃ l₀ ∈ Program.labels p, label l₀ = l) ∨ E c l t

theorem Refinement.mono_exit {CProg AV CV : Type} [WP CProg CV (MachineData → Prop) (Int64 → MachineData → Prop)]
    {J : MachineData → MachineData → Prop} {c : CProg} {a : BlockM MachineData AV} {P : MachineData → Prop}
    {Q : CV → AV → MachineData → Prop} {E E' : Int64 → Int64 → MachineData → Prop}
    (h : ⦃P⦄ c ⪯[Concretization.ofStateRel J] a ⦃Q; E⦄) (hE : ∀ x y t, E x y t → E' x y t) :
    ⦃P⦄ c ⪯[Concretization.ofStateRel J] a ⦃Q; E'⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  refine PartialOrder.rel_trans (wrp_transport h.le_wrp Qa Ea) ?_
  refine WP.wp_monotone (x := c) PartialOrder.rel_refl ?_
  intro x t ht
  simp only [ePosts_ret, Concretization.post_pi, Concretization.ofStateRel_pred] at ht ⊢
  obtain ⟨y, hxy, b, hJ, hb⟩ := ht
  exact ⟨y, hE _ _ _ hxy, b, hJ, hb⟩

/-! ## The control-flow rule -/

theorem wellFounded_accRestrict {α : Type} (S : α → α → Prop) :
    WellFounded fun y x => Acc S x ∧ S y x := by
  refine ⟨fun x => ?_⟩
  by_cases h : Acc S x
  · induction h with
    | intro x _ ih => exact Acc.intro _ fun y ⟨_, hs⟩ => ih y hs
  · exact Acc.intro _ fun _ ⟨ha, _⟩ => absurd ha h

/-- `r` on the values of two `some`s. -/
def OptRel {α : Type} (r : α → α → Prop) : Option α → Option α → Prop
  | some c, some p => r c p
  | _, _ => False

theorem wellFounded_optRel {α : Type} {r : α → α → Prop} (h : WellFounded r) :
    WellFounded (OptRel r) := by
  have hs : ∀ a, Acc (OptRel r) (some a) := fun a => by
    induction a using h.induction with
    | _ a ih =>
      refine Acc.intro _ fun y hy => ?_
      match y, hy with
      | some c, hc => exact ih c hc
  refine ⟨fun x => ?_⟩
  match x with
  | none => exact Acc.intro _ fun y hy => match y, hy with | some _, h => nomatch h
  | some a => exact hs a

theorem ofStateRepr_eq_ofStateRel {Cσ Aσ : Type} (f : Cσ → Aσ) :
    Concretization.ofStateRepr f = Concretization.ofStateRel fun t a => a = f t := by
  have h : (Concretization.ofStateRepr f).pred = (Concretization.ofStateRel fun t a => a = f t).pred := by
    funext P t
    simp only [Concretization.ofStateRepr_pred, Concretization.ofStateRel_pred]
    exact propext ⟨fun h => ⟨f t, rfl, h⟩, fun ⟨_, ha, h⟩ => ha ▸ h⟩
  cases h' : Concretization.ofStateRepr f
  cases h'' : Concretization.ofStateRel fun t a => a = f t
  simp only [h', h''] at h
  subst h
  rfl

section
variable [Host] [FunDecls] (J : MachineData → MachineData → Prop)
  (hJ : ∀ t a, J t a → a.regs = t.regs)
include hJ

open Classical in
theorem wrp_cfg_le_exit {p : Program} [Embeds p] (hs : Program.Separated p = true)
    {cell : Option Label → BlockM MachineData Unit} {s₀ : MachineData}
    (E : Int64 → Int64 → MachineData → Prop)
    (hEstay : ∀ c l v, E c l v → stayIn (s₀.regs.get64 .rsp) v = true → c = l)
    (h : ∀ blk ∈ Program.blocks p, ∀ t,
      ⦃(· = t)⦄ blk.body ⪯[Concretization.ofStateRel J] (cell blk.label)
        ⦃fun _ _ _ => True; BlockExit p (s₀.regs.get64 .rsp) E⦄) :
    (fun t => t = s₀) ⊑ wrp (Concretization.ofStateRel J) p
      (Program.loop p (s₀.regs.get64 .rsp) cell) (fun _ _ => ⊤) E := by
  have hstay : ∀ t a, J t a → (stayIn (s₀.regs.get64 .rsp) a = true ↔ t.StackAtOrBelow s₀) := by
    intro t a hta
    rw [stayIn_iff]
    simp only [MachineData.stackAtOrBelow_def, MachineData.stackBelow_def, hJ t a hta]
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRel_pred] at ht
  obtain ⟨rfl, a₀, hJ₀, hpre⟩ := ht
  let r₀ := t.regs.get64 .rsp
  let st := stayIn r₀
  let T := Program.table p r₀ cell
  let H : (Int64 → MachineData → Prop) × EStack⟨⟩ := (fun a => wp (cfgLoop st T a) Qa Ea, Ea.2)
  let S := (x : Int64 × MachineData) × CfgSafe st T x
  let Inv : Label → MachineData → MachineData × Option S → Prop := fun l u g =>
    J u g.1 ∧ st g.1 = true ∧ wp (cfgLoop st T (label l)) Qa Ea g.1 ∧
      ∃ tr, g.2 = some ⟨(label l, g.1), tr⟩
  let Q : Unit → MachineData → Prop := fun _ u =>
    (Concretization.ofStateRel J).post (fun _ _ => ⊤) Qa () u
  let R : Label × (MachineData × Option S) → Label × (MachineData × Option S) → Prop :=
    InvImage (OptRel (CfgSafe.Child st T)) fun x => x.2.2
  have hentry : (Program.blocks p).head? = some ⟨none, 0, Program.straight (Program.view p).1,
      Program.entryNext p⟩ := by
    rw [Program.blocks_eq]
    unfold Program.entryNext
    rcases (Program.view p).2 with _ | ⟨⟨_, _⟩, _⟩ <;>
      simp only [Program.blocksFrom_nil, Program.blocksFrom_cons, Program.firstLabel_nil,
        Program.firstLabel_cons, List.head?_cons]
  refine Program.WP.cfg_ghost (p := p) (Q := Q)
    (E := EPostsConcretization.ePosts (Concretization.ofStateRel J) E Ea)
    (s₀ := t) (g₀ := (a₀, none)) Inv R
    (InvImage.wf _ (wellFounded_optRel (CfgSafe.wellFounded_child st T))) ?_
  intro blk hmem u g hI
  have hrun : J u g.1 ∧ wp (cell blk.label >>= fun _ => jumpTo st blk.next) Qa H g.1 ∧
      ∃ Pb : Int64 × MachineData → Prop,
        wp (cell blk.label >>= fun _ => jumpTo st blk.next) (fun _ _ => True) (fun l s => Pb (l, s), estack⟨⟩) g.1 ∧
        ∀ a' v, Pb (a', v) → wp (cfgLoop st T a') Qa Ea v → ∃ tr : CfgSafe st T (a', v),
          ∀ l, blk.label = some l → OptRel (CfgSafe.Child st T) (some ⟨(a', v), tr⟩) g.2 := by
    cases hl : blk.label with
    | none =>
      rw [hl] at hI
      obtain ⟨hu, hg⟩ := hI
      subst hu hg
      have hblk : blk = ⟨none, 0, Program.straight (Program.view p).1, Program.entryNext p⟩ := by
        refine Program.block_unique Program.labels_nodup_of_embeds hmem ?_ hl
        exact List.mem_of_mem_head? hentry
      have hw : wp (cell none >>= fun _ => jumpTo st blk.next) Qa H a₀ := by
        rw [hblk]
        simpa only [Program.loop, BlockLoop.wp_tryCatch] using hpre
      refine ⟨hJ₀, hw, fun _ => True, ?_, fun a' v _ hwv =>
        ⟨Classical.choice (nonempty_cfgSafe st T hwv), fun _ h => nomatch h⟩⟩
      rw [wp_BlockM_eq] at hw ⊢
      refine (Demonic.mono _ (fun r _ => ?_) hw)
      rcases r with ⟨_ | _, _⟩ <;> trivial
    | some l =>
      rw [hl] at hI
      obtain ⟨hJa, hst, hw, tr, hg⟩ := hI
      have hTb := Program.table_get?_label (r₀ := r₀) (cell := cell) hs hmem hl
      rw [wp_cfgLoop_some st T Qa Ea hTb hst] at hw
      rw [hl] at hTb hw
      cases tr with
      | intro P hP next =>
        exact ⟨hJa, hw, P, hP _ hst hTb, fun a' v hy _ =>
          ⟨next (a', v) hy, fun _ _ => by rw [hg]; exact ⟨hy, rfl⟩⟩⟩
  obtain ⟨hJa, hw, Pb, hPb, hdec⟩ := hrun
  let c := cell blk.label
  rw [WPMonadExact.wp_bind_eq] at hw hPb
  let Qa' : Unit → MachineData → Prop := fun _ st' =>
    wp (jumpTo st blk.next : BlockM MachineData Unit) Qa H st' ∧
      wp (jumpTo st blk.next : BlockM MachineData Unit) (fun _ _ => True)
        (fun l s => Pb (l, s), estack⟨⟩) st'
  let Ea' : (Int64 → MachineData → Prop) × EStack⟨⟩ :=
    (fun a' st' => wp (cfgLoop st T a') Qa Ea st' ∧ Pb (a', st'), Ea.2)
  have hpre' : wp c Qa' Ea' g.1 := BlockLoop.wp_and hw hPb
  have hb := wrp_transport (h blk hmem u).le_wrp Qa' Ea'
  have hmeet : ((fun t' => t' = u) ⊓ (Concretization.ofStateRel J).pred (wp c Qa' Ea')) u := by
    simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRel_pred]
    exact ⟨trivial, g.1, hJa, hpre'⟩
  have hwp := hb u hmeet
  have hnext : ∀ l' w b, J w b → st b = true → wp (cfgLoop st T (label l')) Qa Ea b →
      Pb (label l', b) → ∃ g', Inv l' w g' ∧ Program.GhostDec R blk.label g l' g' := by
    intro l' w b hJb hsb hE hy
    obtain ⟨tr, htr⟩ := hdec (label l') b hy hE
    refine ⟨(b, some ⟨(label l', b), tr⟩), ⟨hJb, hsb, hE, tr, rfl⟩, ?_⟩
    cases hbl : blk.label with
    | none => trivial
    | some l₀ => exact htr l₀ hbl
  have hjump : ∀ v b c a', J v b → BlockExit p r₀ E c a' v → wp (cfgLoop st T a') Qa Ea b →
      Pb (a', b) →
      Program.Intercept (Program.labels p) t
        (fun l _ s' => ∃ g', Inv l s' g' ∧ Program.GhostDec R blk.label g l g')
        (EPostsConcretization.ePosts (Concretization.ofStateRel J) E Ea) c v := by
    intro v b c a' hJv hrel hE hy
    have hsvb : st b = stayIn r₀ v := by
      simp only [st, stayIn, hJ v b hJv]
    cases hsv : st b with
    | false =>
      rw [wp_cfgLoop_leave st T Qa Ea hsv] at hE
      have hEc : E c a' v := by
        rcases hrel with ⟨h1, -, -⟩ | h1
        · rw [← hsvb, hsv] at h1; exact nomatch h1
        · exact h1
      refine Program.Intercept.intro (Or.inr ⟨?_, fun _ _ _ => ?_⟩)
      · show (Concretization.ofStateRel J).post E Ea.1 c v
        simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
          meet_prop_eq_and, Concretization.ofStateRel_pred]
        exact ⟨a', hEc, b, hJv, hE⟩
      · have h1 : ¬ v.StackAtOrBelow t := fun h2 => by
          have := (hstay v b hJv).mpr h2
          simp only [st, r₀] at hsv
          rw [hsv] at this
          exact nomatch this
        simpa only [MachineData.stackAtOrBelow_def, Classical.not_not] using h1
    | true =>
    have hca : c = a' := by
      rcases hrel with ⟨-, h, -⟩ | h
      · exact h
      · exact hEstay _ _ _ h (by rw [← hsvb]; exact hsv)
    subst hca
    cases hT : T.get? c with
    | none =>
      rw [wp_cfgLoop_none st T Qa Ea hT] at hE
      have hEc : E c c v := by
        rcases hrel with ⟨-, -, l₀, hl₀, hla⟩ | h
        · exact absurd hla (Program.table_get?_none hT hl₀)
        · exact h
      refine Program.Intercept.intro (Or.inr ⟨?_, fun l hl ha => ?_⟩)
      · show (Concretization.ofStateRel J).post E Ea.1 c v
        simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
          meet_prop_eq_and, Concretization.ofStateRel_pred]
        exact ⟨c, hEc, b, hJv, hE⟩
      · exact absurd ha (Program.table_get?_none hT hl)
    | some bb =>
      obtain ⟨blk', hblk', l, hl, ha, -⟩ := Program.table_get?_some hT
      subst ha
      exact Program.Intercept.intro (Or.inl ⟨(hstay v b hJv).mp hsv, l, rfl,
        Program.label_mem_labels hblk' hl, hnext l v b hJv hsv hE hy⟩)
  refine Program.wp_mono (fun u' hu => ?_) (fun u' hu => ?_) hwp
  · change (Concretization.ofStateRel J).post (fun _ _ _ => True) Qa' () u'.data at hu
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
      meet_prop_eq_and, Concretization.ofStateRel_pred] at hu
    obtain ⟨-, -, b, hJb, hQ, hc⟩ := hu
    show Program.GhostNext Inv Q R blk.label g blk.next u'.data
    cases hn : blk.next with
    | none =>
      rw [hn, jumpTo_none, WPMonadExact.wp_pure_eq] at hQ
      simp only [Program.GhostNext, Q, Concretization.post, iSup_apply, iSup_prop_eq_exists,
        meet_apply, meet_prop_eq_and, top_apply, top_prop_eq, Concretization.ofStateRel_pred]
      exact ⟨(), trivial, b, hJb, hQ⟩
    | some l' =>
      rw [hn, jumpTo_some, AInstr.wp_branch] at hQ hc
      simp only [↓reduceIte] at hQ hc
      obtain ⟨hsu, hQ⟩ := hQ
      exact hnext l' u'.data b hJb hsu hQ hc.2
  · change (Concretization.ofStateRel J).post (BlockExit p r₀ E) Ea'.1 u'.pc u'.data at hu
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
      meet_prop_eq_and, Concretization.ofStateRel_pred] at hu
    obtain ⟨a', hrel, b, hJb, hE, hc⟩ := hu
    exact hjump u'.data b u'.pc a' hJb hrel hE hc

theorem wrp_cfg_le_rel {p : Program} [Embeds p] (hs : Program.Separated p = true)
    {cell : Option Label → BlockM MachineData Unit} {s₀ : MachineData} {ra : Int64}
    (h : ∀ blk ∈ Program.blocks p, ∀ t,
      ⦃(· = t)⦄ blk.body ⪯[Concretization.ofStateRel J] (cell blk.label)
        ⦃fun _ _ _ => True; AddrRel (s₀.regs.get64 .rsp) ra⦄) :
    (fun t => t = s₀) ⊑ wrp (Concretization.ofStateRel J) p
      (Program.loop p (s₀.regs.get64 .rsp) cell) (fun _ _ => ⊤) (AddrRel (s₀.regs.get64 .rsp) ra) :=
  wrp_cfg_le_exit J hJ hs _ (fun _ _ _ h _ => h) fun blk hb t =>
    Refinement.mono_exit (h blk hb t) fun _ _ _ h => Or.inr h
end

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
  rw [ofStateRepr_eq_ofStateRel] at h ⊢
  exact wrp_cfg_le_rel _ (fun t a hta => by subst hta; exact habs t) hs h

/-- The control-flow rule as a spec: the abstract program is the block loop over the table of the
text, whose cells `distill` fills block by block. -/
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

section
variable [Host] [FunDecls]

theorem refines_cfg_exit (J : MachineData → MachineData → Prop) (hJ : ∀ t a, J t a → a.regs = t.regs)
    {p : Program} [Embeds p] {r₀ : BitVec 64} (E : Int64 → Int64 → MachineData → Prop)
    (hE : ∀ c l v, E c l v → stayIn r₀ v = true → c = l)
    (tbl : Table (Option Label) (BlockM MachineData Unit)) (hs : Program.Separated p = true := by decide +kernel)
    (h : ∀ blk ∈ Program.blocks p, ∀ t,
      ⦃(· = t)⦄ blk.body ⪯[Concretization.ofStateRel J] (Table.get tbl blk.label)
        ⦃fun _ _ _ => True; BlockExit p r₀ E⦄) :
    ⦃fun s => s.regs.get64 .rsp = r₀⦄ p ⪯[Concretization.ofStateRel J]
      (Program.loop p r₀ (Table.get tbl)) ⦃fun _ _ => ⊤; E⦄ :=
  ⟨fun t hrt => by
    subst hrt
    exact wrp_cfg_le_exit J hJ hs E hE (s₀ := t) h t rfl⟩

end

section
variable [Host] [FunDecls]

theorem refines_cfg_rel (J : MachineData → MachineData → Prop) (hJ : ∀ t a, J t a → a.regs = t.regs)
    {p : Program} [Embeds p] {r₀ : BitVec 64} {ra : Int64}
    (tbl : Table (Option Label) (BlockM MachineData Unit)) (hs : Program.Separated p = true := by decide +kernel)
    (h : ∀ blk ∈ Program.blocks p, ∀ t,
      ⦃(· = t)⦄ blk.body ⪯[Concretization.ofStateRel J] (Table.get tbl blk.label)
        ⦃fun _ _ _ => True; AddrRel r₀ ra⦄) :
    ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ p ⪯[Concretization.ofStateRel J]
      (Program.loop p r₀ (Table.get tbl)) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄ :=
  ⟨fun t ⟨hrt, _⟩ => by
    subst hrt
    exact wrp_cfg_le_rel J hJ hs (s₀ := t) h t rfl⟩

end

end Distillery.Kraken
