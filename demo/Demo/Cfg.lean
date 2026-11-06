import Demo.Kraken
import Ascent.Table
import Kraken.StateCfg
import Ascent.UB.StateT
import Ascent.UB.WhileLoop

/-!
# Control-flow graphs

`cfgLoop ablock next` is the abstract program of a kraken text with labels: a loop over the
`CfgLabel`s that runs the abstract block of the label, continues at the fallthrough `next l` on a
normal exit and at the thrown label on a jump, and stops at `.exit`. A block program lives in
`BlockM Aσ`, and a jump is the exception that carries its target.

`wrp_cfg` refines a text to `cfgLoop ablock next .entry` from one refinement per block, in the form
of kraken's funspec: the text starts at `s.push64 ra`, and its return pairs with the abstract
exception `.exit` through `RetRel s ra`.
-/

open Std.WP Lean.Order Ascent
open scoped Program.WP

/-! ## The blocks of a text as a list -/

def Program.blocksFrom (b : CfgLabel) (j : Nat) (body : Program) :
    List (Label × Program) → List Program.Block
  | [] => [⟨b, j, body, .exit⟩]
  | (l, body') :: bs => ⟨b, j, body, .label l⟩ :: Program.blocksFrom (.label l) (j + 1) body' bs

def Program.blocks (p : Program) : List Program.Block :=
  Program.blocksFrom .entry 0 (Program.view p).1 (Program.view p).2

theorem Program.forallBlocksFrom_iff {P : Program.Block → Prop} :
    ∀ {b : CfgLabel} {j : Nat} {body : Program} {bs : List (Label × Program)},
      Program.forallBlocksFrom P b j body bs ↔ ∀ blk ∈ Program.blocksFrom b j body bs, P blk
  | _, _, _, [] => by simp [Program.forallBlocksFrom, Program.blocksFrom]
  | _, _, _, (l, b') :: bs => by
    simp only [Program.forallBlocksFrom, Program.blocksFrom, List.forall_mem_cons]
    exact and_congr Iff.rfl Program.forallBlocksFrom_iff

theorem Program.forallBlocks_iff {p : Program} {P : Program.Block → Prop} :
    Program.ForallBlocks p P ↔ ∀ blk ∈ Program.blocks p, P blk :=
  Program.forallBlocksFrom_iff

theorem Program.label_ne_exit_of_mem_blocksFrom {b : CfgLabel} (hb : b ≠ .exit) :
    ∀ {j : Nat} {body : Program} {bs : List (Label × Program)} {blk : Program.Block},
      blk ∈ Program.blocksFrom b j body bs → blk.label ≠ .exit
  | _, _, [], blk, h => by
    simp only [Program.blocksFrom, List.mem_singleton] at h
    subst h
    exact hb
  | _, _, (l, b') :: bs, blk, h => by
    simp only [Program.blocksFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact hb
    · exact Program.label_ne_exit_of_mem_blocksFrom (by simp) h

theorem Program.label_ne_exit_of_mem_blocks {p : Program} {blk : Program.Block}
    (h : blk ∈ Program.blocks p) : blk.label ≠ .exit :=
  Program.label_ne_exit_of_mem_blocksFrom (by simp) h

@[vcgen_simp] theorem Program.view_nil' : Program.view [] = ([], []) := rfl
@[vcgen_simp] theorem Program.view_cons_label (l : Label) (p : Program) :
    Program.view (.label l :: p) = ([], (l, (Program.view p).1) :: (Program.view p).2) := rfl
@[vcgen_simp] theorem Program.view_cons_instr (i : Instr) (p : Program) :
    Program.view (.instr i :: p) = (.instr i :: (Program.view p).1, (Program.view p).2) := rfl
@[vcgen_simp] theorem Program.view_cons_byteArray (a : ByteArray) (p : Program) :
    Program.view (.byteArray a :: p) = (.byteArray a :: (Program.view p).1, (Program.view p).2) :=
  rfl
@[vcgen_simp] theorem Program.blocks_eq (p : Program) :
    Program.blocks p = Program.blocksFrom .entry 0 (Program.view p).1 (Program.view p).2 := rfl
@[vcgen_simp] theorem Program.blocksFrom_nil (b : CfgLabel) (j : Nat) (body : Program) :
    Program.blocksFrom b j body [] = [⟨b, j, body, .exit⟩] := rfl
@[vcgen_simp] theorem Program.blocksFrom_cons (b : CfgLabel) (j : Nat) (body : Program)
    (l : Label) (body' : Program) (bs : List (Label × Program)) :
    Program.blocksFrom b j body ((l, body') :: bs)
      = ⟨b, j, body, .label l⟩ :: Program.blocksFrom (.label l) (j + 1) body' bs := rfl
attribute [vcgen_simp] List.forall_mem_cons List.forall_mem_nil

/-- The fallthrough target of the block at `l` in a list of blocks, `.exit` for a label without a
block. -/
def Program.nextIn : List Program.Block → CfgLabel → CfgLabel
  | [], _ => .exit
  | blk :: bs, l => if blk.label = l then blk.next else Program.nextIn bs l

@[vcgen_simp, grind =] theorem Program.nextIn_nil (l : CfgLabel) : Program.nextIn [] l = .exit := rfl
@[vcgen_simp, grind =] theorem Program.nextIn_cons (blk : Program.Block) (bs : List Program.Block)
    (l : CfgLabel) :
    Program.nextIn (blk :: bs) l = if blk.label = l then blk.next else Program.nextIn bs l := rfl

theorem Program.nextIn_eq_find? (bs : List Program.Block) (l : CfgLabel) :
    Program.nextIn bs l = ((bs.find? fun blk => blk.label = l).map (·.next)).getD .exit := by
  induction bs with
  | nil => rfl
  | cons blk bs ih =>
    by_cases h : blk.label = l
    · simp [Program.nextIn, h]
    · simp [Program.nextIn, h, ih]

/-- The fallthrough target of the block at `l`. -/
def Program.next (p : Program) (l : CfgLabel) : CfgLabel := Program.nextIn (Program.blocks p) l

@[vcgen_simp, grind =] theorem Program.next_eq (p : Program) (l : CfgLabel) :
    Program.next p l = Program.nextIn (Program.blocks p) l := rfl

theorem Program.label_mem_blocksFrom {b : CfgLabel} :
    ∀ {j : Nat} {body : Program} {bs : List (Label × Program)} {blk : Program.Block},
      blk ∈ Program.blocksFrom b j body bs → blk.label = b ∨ ∃ lb ∈ bs, blk.label = .label lb.1
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

theorem Program.find?_blocksFrom {b : CfgLabel} :
    ∀ {j : Nat} {body : Program} {bs : List (Label × Program)}, (bs.map (·.1)).Nodup →
      (∀ lb ∈ bs, b ≠ .label lb.1) → ∀ {blk : Program.Block}, blk ∈ Program.blocksFrom b j body bs →
        (Program.blocksFrom b j body bs).find? (fun blk' => blk'.label = blk.label) = some blk
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
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      rw [Program.blocksFrom, List.find?_cons_of_neg (by simpa using hne)]
      exact Program.find?_blocksFrom hnd.2 (fun lb hlb heq => hnd.1 ⟨lb, hlb, (CfgLabel.label.inj heq).symm⟩) h

/-- With distinct labels, the fallthrough target of a block is its successor in the text. -/
theorem Program.next_eq_of_nodup {p : Program} (hnd : (Program.labels p).Nodup) {blk : Program.Block}
    (h : blk ∈ Program.blocks p) : Program.next p blk.label = blk.next := by
  rw [Program.labels_view] at hnd
  rw [Program.next, Program.nextIn_eq_find?]
  unfold Program.blocks
  rw [Program.find?_blocksFrom hnd (fun _ _ => CfgLabel.noConfusion) h]
  rfl

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

theorem admissible_wp_imp (Q : α → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ)
    (R : Prop) : Lean.Order.admissible fun u : BlockM σ α => wp u Q E s → R := by
  intro ch hch hall hw
  have := WPCont.wp_csup (Prog := BlockM σ α) hch Q E s hw
  simp only [iSup_apply, iSup_prop_eq_exists] at this
  obtain ⟨⟨u, hu⟩, hwu⟩ := this
  exact hall u hu hwu

end


/-- The fixpoint, at the state-passing type that carries the `CCPO`. -/
def cfgFix {Aσ : Type} (ablock : CfgLabel → BlockM Aσ Unit) (next : CfgLabel → CfgLabel)
    (l : CfgLabel) (s : Aσ) : UB (Except CfgLabel Unit × Aσ) :=
  if l = .exit then pure (.ok (), s) else
    (ablock l).run.run s >>= fun p =>
      match p.1 with
      | .ok _ => cfgFix ablock next (next l) p.2
      | .error l' => if l' = .exit then pure (.error .exit, p.2) else cfgFix ablock next l' p.2
partial_fixpoint

def cfgLoop {Aσ : Type} (ablock : CfgLabel → BlockM Aσ Unit) (next : CfgLabel → CfgLabel)
    (l : CfgLabel) : BlockM Aσ Unit :=
  cfgFix ablock next l

section
variable {Aσ : Type} (ablock : CfgLabel → BlockM Aσ Unit) (next : CfgLabel → CfgLabel)

def cfgStep (f : CfgLabel → BlockM Aσ Unit) (l : CfgLabel) : BlockM Aσ Unit :=
  show Aσ → UB (Except CfgLabel Unit × Aσ) from fun s =>
    if l = .exit then pure (Except.ok (), s) else do
      let p ← (ExceptT.run (ablock l)).run s
      match p.fst with
      | Except.ok _ => (f (next l)).run.run p.snd
      | Except.error l' =>
        if l' = .exit then pure (Except.error .exit, p.snd) else (f l').run.run p.snd

theorem cfgStep_run_of_ne (f : CfgLabel → BlockM Aσ Unit) {l : CfgLabel} (hl : l ≠ .exit) (s : Aσ) :
    (cfgStep ablock next f l).run.run s = ((ablock l).run.run s >>= fun p =>
      match p.fst with
      | Except.ok _ => (f (next l)).run.run p.snd
      | Except.error l' =>
        if l' = .exit then pure (Except.error .exit, p.snd) else (f l').run.run p.snd) := by
  show (if l = .exit then _ else _) = _
  rw [if_neg hl]

theorem cfgStep_exit (f : CfgLabel → BlockM Aσ Unit) : cfgStep ablock next f .exit = pure () := rfl

theorem cfgLoop_induct (motive : (CfgLabel → BlockM Aσ Unit) → Prop) (hadm : admissible motive)
    (h : ∀ f, motive f → motive (cfgStep ablock next f)) : motive (cfgLoop ablock next) :=
  cfgFix.fixpoint_induct ablock next motive hadm h

theorem wp_cfgStep (f : CfgLabel → BlockM Aσ Unit) {l : CfgLabel} (hl : l ≠ .exit)
    (Qa : Unit → Aσ → Prop) (Ea : (CfgLabel → Aσ → Prop) × EStack⟨⟩) (s : Aσ) :
    wp (cfgStep ablock next f l) Qa Ea s
      = wp (ablock l) (fun _ => wp (f (next l)) Qa Ea)
          (fun l' => if l' = .exit then Ea.1 .exit else wp (f l') Qa Ea, Ea.2) s := by
  rw [wp_BlockM_eq, wp_BlockM_eq]
  rw [cfgStep_run_of_ne _ _ _ hl]
  rcases (ablock l).run.run s with _ | ⟨l' | _, s'⟩
  · rfl
  · simp only [UB.some_bind]
    by_cases h : l' = .exit
    · subst h; simp only [↓reduceIte]; rfl
    · simp only [h, ↓reduceIte]; rw [wp_BlockM_eq]
  · simp only [UB.some_bind]; rw [wp_BlockM_eq]

theorem cfgLoop_eq_cfgStep : cfgLoop ablock next = cfgStep ablock next (cfgLoop ablock next) := by
  funext l
  show (cfgFix ablock next l : Aσ → UB (Except CfgLabel Unit × Aσ)) = cfgStep ablock next _ l
  funext s
  rw [cfgFix]
  rfl

end

section
variable {Aσ : Type} (ablock : CfgLabel → BlockM Aσ Unit) (next : CfgLabel → CfgLabel)
  (Qa : Unit → Aσ → Prop) (Ea : (CfgLabel → Aσ → Prop) × EStack⟨⟩) (s : Aσ)

theorem cfgLoop_run (l : CfgLabel) : (cfgLoop ablock next l).run.run s = cfgFix ablock next l s :=
  rfl

theorem wp_cfgLoop_exit : wp (cfgLoop ablock next .exit) Qa Ea s = Qa () s := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, cfgLoop_run, cfgFix]
  simp only [eq_self, ↓reduceIte, UB.wp_pure_eq]
  rfl

/-- The exception post of one block: the loop continues at a thrown label, and `.exit` is final. -/
def cfgEPosts (l' : CfgLabel) : Aσ → Prop :=
  if l' = .exit then Ea.1 .exit else wp (cfgLoop ablock next l') Qa Ea

theorem wp_cfgLoop {l : CfgLabel} (hl : l ≠ .exit) :
    wp (cfgLoop ablock next l) Qa Ea s
      = wp (ablock l) (fun _ => wp (cfgLoop ablock next (next l)) Qa Ea)
          (cfgEPosts ablock next Qa Ea, Ea.2) s := by
  rw [congrFun (cfgLoop_eq_cfgStep ablock next) l, wp_cfgStep _ _ _ hl]
  rfl

theorem wp_cfgLoop_exit_fn : wp (cfgLoop ablock next .exit) Qa Ea = Qa () :=
  funext (wp_cfgLoop_exit ablock next Qa Ea)

theorem wp_cfgLoop_fn {l : CfgLabel} (hl : l ≠ .exit) :
    wp (cfgLoop ablock next l) Qa Ea
      = wp (ablock l) (fun _ => wp (cfgLoop ablock next (next l)) Qa Ea)
          (cfgEPosts ablock next Qa Ea, Ea.2) :=
  funext fun s => wp_cfgLoop ablock next Qa Ea s hl

theorem cfgEPosts_label (l : Label) :
    cfgEPosts ablock next Qa Ea (.label l) = wp (cfgLoop ablock next (.label l)) Qa Ea := by
  simp only [cfgEPosts, reduceCtorEq, ↓reduceIte]

theorem cfgEPosts_exit : cfgEPosts ablock next Qa Ea .exit = Ea.1 .exit := by
  simp only [cfgEPosts, ↓reduceIte]

end

/-! ## The number of blocks a run executes -/

section
variable {Aσ : Type} (ablock : CfgLabel → BlockM Aσ Unit) (next : CfgLabel → CfgLabel)

def count : Nat → CfgLabel → Aσ → UB Nat
  | 0, _, _ => UB.fail
  | n + 1, l, st =>
    if l = .exit then pure 0 else
      (ablock l).run.run st >>= fun p =>
        match p.1 with
        | .ok _ => (· + 1) <$> count n (next l) p.2
        | .error l' => if l' = .exit then pure 1 else (· + 1) <$> count n l' p.2

theorem count_of_cfgFix : ∀ (l : CfgLabel) (st : Aσ) (r : Except CfgLabel Unit × Aσ),
    cfgFix ablock next l st = some r → ∃ n k, count ablock next n l st = some k := by
  refine cfgFix.fixpoint_induct ablock next
    (fun f => ∀ l st r, f l st = some r → ∃ n k, count ablock next n l st = some k) ?_ ?_
  · refine admissible_pi_apply
      (fun l (g : Aσ → UB (Except CfgLabel Unit × Aσ)) =>
        ∀ st r, g st = some r → ∃ n k, count ablock next n l st = some k) fun l => ?_
    refine admissible_pi_apply
      (fun st (u : UB (Except CfgLabel Unit × Aσ)) =>
        ∀ r, u = some r → ∃ n k, count ablock next n l st = some k) fun st => ?_
    exact admissible_flatOrder (b := (none : Option (Except CfgLabel Unit × Aσ)))
      (fun u => ∀ r, (show UB (Except CfgLabel Unit × Aσ) from u) = some r →
        ∃ n k, count ablock next n l st = some k)
      (fun _ h => nomatch h)
  · intro f ih l st r h
    dsimp only at h
    by_cases hl : l = .exit
    · subst hl
      refine ⟨0 + 1, 0, ?_⟩
      rw [count]
      simp only [eq_self, ↓reduceIte, UB.pure_eq]
      try rfl
    · simp only [hl, ↓reduceIte] at h
      obtain ⟨⟨r', st'⟩, hp, hr⟩ := (UB.bind_eq_some _ _ _).mp h
      rcases r' with l' | _
      · simp only at hr
        by_cases hl' : l' = .exit
        · subst hl'
          refine ⟨0 + 1, 1, ?_⟩
          rw [count, hp, UB.some_bind]
          simp only [hl, eq_self, ↓reduceIte, UB.pure_eq]
          try rfl
        · simp only [hl', ↓reduceIte] at hr
          obtain ⟨n, k, hk⟩ := ih l' st' r hr
          refine ⟨n + 1, k + 1, ?_⟩
          rw [count, hp, UB.some_bind]
          simp only [hl, hl', ↓reduceIte, hk, UB.map_some]
          try rfl
      · simp only at hr
        obtain ⟨n, k, hk⟩ := ih (next l) st' r hr
        refine ⟨n + 1, k + 1, ?_⟩
        rw [count, hp, UB.some_bind]
        simp only [hl, ↓reduceIte, hk, UB.map_some]
        try rfl

theorem count_unique : ∀ (n n' : Nat) (l : CfgLabel) (st : Aσ) (k k' : Nat),
    count ablock next n l st = some k → count ablock next n' l st = some k' → k = k'
  | 0, _, _, _, _, _, h, _ => by simp [count, UB.fail_eq] at h
  | _ + 1, 0, _, _, _, _, _, h' => by simp [count, UB.fail_eq] at h'
  | n + 1, n' + 1, l, st, k, k', h, h' => by
    rw [count] at h h'
    by_cases hl : l = .exit
    · subst hl
      simp only [eq_self, ↓reduceIte, UB.pure_eq] at h h'
      have := Option.some.inj h
      have := Option.some.inj h'
      omega
    · simp only [hl, ↓reduceIte] at h h'
      obtain ⟨⟨r, st'⟩, hp, hr⟩ := (UB.bind_eq_some _ _ _).mp h
      obtain ⟨⟨r', st''⟩, hp', hr'⟩ := (UB.bind_eq_some _ _ _).mp h'
      rw [hp] at hp'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp')
      rcases r with l' | _
      · simp only at hr hr'
        by_cases hl' : l' = .exit
        · subst hl'
          simp only [eq_self, ↓reduceIte, UB.pure_eq] at hr hr'
          have := Option.some.inj hr
          have := Option.some.inj hr'
          omega
        · simp only [hl', ↓reduceIte] at hr hr'
          obtain ⟨k₁, hk₁, rfl⟩ := (UB.map_eq_some _ _ _).mp hr
          obtain ⟨k₂, hk₂, rfl⟩ := (UB.map_eq_some _ _ _).mp hr'
          rw [count_unique n n' l' st' k₁ k₂ hk₁ hk₂]
      · simp only at hr hr'
        obtain ⟨k₁, hk₁, rfl⟩ := (UB.map_eq_some _ _ _).mp hr
        obtain ⟨k₂, hk₂, rfl⟩ := (UB.map_eq_some _ _ _).mp hr'
        rw [count_unique n n' (next l) st' k₁ k₂ hk₁ hk₂]

open Classical in
noncomputable def steps (l : CfgLabel) (st : Aσ) : Nat :=
  if h : ∃ k n, count ablock next n l st = some k then Classical.choose h else 0

theorem steps_eq {n : Nat} {l : CfgLabel} {st : Aσ} {k : Nat}
    (h : count ablock next n l st = some k) : steps ablock next l st = k := by
  have hex : ∃ k n, count ablock next n l st = some k := ⟨k, n, h⟩
  simp only [steps, hex, ↓reduceDIte]
  obtain ⟨n', hn'⟩ := Classical.choose_spec hex
  exact count_unique ablock next n' n l st _ k hn' h

theorem steps_lt_of_ok {l : CfgLabel} {st st' : Aσ} (hl : l ≠ .exit)
    (hrun : (ablock l).run.run st = some (.ok (), st'))
    {r : Except CfgLabel Unit × Aσ} (hfix : cfgFix ablock next l st = some r) :
    steps ablock next (next l) st' < steps ablock next l st := by
  obtain ⟨n, k, hk⟩ := count_of_cfgFix ablock next l st r hfix
  cases n with
  | zero => simp [count, UB.fail_eq] at hk
  | succ n =>
    have hk0 := hk
    rw [count, hrun, UB.some_bind] at hk
    simp only [hl, ↓reduceIte] at hk
    obtain ⟨k', hk', rfl⟩ := (UB.map_eq_some _ _ _).mp hk
    rw [steps_eq ablock next hk0, steps_eq ablock next hk']
    omega

theorem steps_lt_of_error {l l' : CfgLabel} {st st' : Aσ} (hl : l ≠ .exit) (hl' : l' ≠ .exit)
    (hrun : (ablock l).run.run st = some (.error l', st'))
    {r : Except CfgLabel Unit × Aσ} (hfix : cfgFix ablock next l st = some r) :
    steps ablock next l' st' < steps ablock next l st := by
  obtain ⟨n, k, hk⟩ := count_of_cfgFix ablock next l st r hfix
  cases n with
  | zero => simp [count, UB.fail_eq] at hk
  | succ n =>
    have hk0 := hk
    rw [count, hrun, UB.some_bind] at hk
    simp only [hl, hl', ↓reduceIte] at hk
    obtain ⟨k', hk', rfl⟩ := (UB.map_eq_some _ _ _).mp hk
    rw [steps_eq ablock next hk0, steps_eq ablock next hk']
    omega

end

/-! ## The block relations -/

def RetRel (s : MachineData) (ra : Int64) : Int64 → CfgLabel → MachineData → Prop :=
  fun a l' s' => a = ra ∧ l' = .exit ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp

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

/-! ## The control-flow rule -/

section
variable {Aσ : Type} (abs : MachineData → Aσ)

theorem decreases_of_steps_lt {ablock : CfgLabel → BlockM Aσ Unit} {next : CfgLabel → CfgLabel}
    {l b : CfgLabel} {i j : Nat} {t s : MachineData}
    (h : b ≠ .exit → steps ablock next b (abs s) < steps ablock next l (abs t)) :
    Program.Decreases (fun l t => steps ablock next (.label l) (abs t)) l i t b j s := by
  cases l <;> cases b <;> simp only [Program.Decreases]
  exact Or.inl (h (by simp))

end

section
variable [Host] [FunDecls] {Aσ : Type} (abs : MachineData → Aσ)

theorem wrp_cfg_le {p : Program} (next : CfgLabel → CfgLabel)
    (hnext : ∀ blk ∈ Program.blocks p, next blk.label = blk.next)
    {ablock : CfgLabel → BlockM Aσ Unit} {s : MachineData} {ra : Int64}
    (h : ∀ blk ∈ Program.blocks p, ∀ t, SameStackFrame (s.push64 ra) t →
      ⦃(· = t)⦄ blk.body ⪯[Concretization.ofStateRepr abs] (ablock blk.label)
        ⦃FallRel (s.push64 ra); JumpRel p (s.push64 ra)⦄) :
    (fun t => t = s.push64 ra) ⊑ wrp (Concretization.ofStateRepr abs) p
      (cfgLoop ablock next .entry) (fun _ _ => ⊤) (RetRel s ra) := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred] at ht
  obtain ⟨rfl, hpre⟩ := ht
  let I : CfgLabel → MachineData → Prop := fun l t =>
    wp (cfgLoop ablock next l) Qa Ea (abs t) ∧ SameStackFrame (s.push64 ra) t
  have hcfg := Program.WP.cfg (p := p)
    (E := EPostsConcretization.ePosts (Concretization.ofStateRepr abs) (RetRel s ra) Ea)
    (s₀ := s.push64 ra) I (fun l t => steps ablock next (.label l) (abs t)) ?_
    ⟨hpre, rfl, rfl⟩
  · refine Program.wp_mono (fun u hu => ?_) (fun _ hu => hu) hcfg
    obtain ⟨hQ, -⟩ := hu
    rw [wp_cfgLoop_exit_fn] at hQ
    show (Concretization.ofStateRepr abs).post (fun _ _ => ⊤) Qa () u.data
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
      meet_prop_eq_and, top_apply, top_prop_eq, Concretization.ofStateRepr_pred]
    exact ⟨(), trivial, hQ⟩
  · refine Program.forallBlocks_iff.mpr fun blk hmem t hI => ?_
    intro I'
    obtain ⟨hIt, hst⟩ := hI
    have hl := Program.label_ne_exit_of_mem_blocks hmem
    have hfix : ∃ r, cfgFix ablock next blk.label (abs t) = some r := by
      rw [wp_BlockM_eq, cfgLoop_run] at hIt
      revert hIt
      cases cfgFix ablock next blk.label (abs t) <;> intro hIt
      · exact hIt.elim
      · exact ⟨_, rfl⟩
    obtain ⟨r, hfix⟩ := hfix
    rw [wp_cfgLoop_fn ablock next Qa Ea hl, wp_BlockM_eq] at hIt
    let Qa' : Unit → Aσ → Prop := fun _ st' =>
      wp (cfgLoop ablock next (next blk.label)) Qa Ea st'
        ∧ (ablock blk.label).run.run (abs t) = some (.ok (), st')
    let Ea' : (CfgLabel → Aσ → Prop) × EStack⟨⟩ :=
      (fun l' st' => cfgEPosts ablock next Qa Ea l' st'
        ∧ (ablock blk.label).run.run (abs t) = some (.error l', st'), Ea.2)
    have hpre' : wp (ablock blk.label) Qa' Ea' (abs t) := by
      rw [wp_BlockM_eq]
      revert hIt
      rcases hrun : (ablock blk.label).run.run (abs t) with _ | ⟨l' | _, st'⟩ <;> intro hIt
      · exact hIt.elim
      · exact ⟨hIt, hrun⟩
      · exact ⟨hIt, hrun⟩
    have hb := wrp_transport (h blk hmem t hst).le_wrp Qa' Ea'
    have hmeet : ((fun t' => t' = t) ⊓ (Concretization.ofStateRepr abs).pred
        (wp (ablock blk.label) Qa' Ea')) t := by
      simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]
      exact ⟨trivial, hpre'⟩
    have hwp := hb t hmeet
    refine Program.wp_mono (fun u hu => ?_) (fun u hu => ?_) hwp
    · show I' blk.next (blk.idx + 1) () u.data
      change (Concretization.ofStateRepr abs).post (FallRel (s.push64 ra)) Qa' () u.data at hu
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, Concretization.ofStateRepr_pred, FallRel] at hu
      obtain ⟨-, hst', hQ, hrun⟩ := hu
      rw [hnext blk hmem] at hQ
      refine ⟨⟨hQ, hst'⟩, decreases_of_steps_lt abs fun _ => ?_⟩
      rw [← hnext blk hmem]
      exact steps_lt_of_ok ablock next hl hrun hfix
    · show Program.Intercept (Program.labels p) (s.push64 ra) I'
        (EPostsConcretization.ePosts (Concretization.ofStateRepr abs) (RetRel s ra) Ea)
        u.pc u.data
      change (Concretization.ofStateRepr abs).post (JumpRel p (s.push64 ra)) Ea'.1
        u.pc u.data at hu
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, Concretization.ofStateRepr_pred, JumpRel] at hu
      obtain ⟨l', hrel, hE, hrun⟩ := hu
      rcases hrel with ⟨l, hmem', rfl, ha, hst'⟩ | ⟨rfl, ha, hrsp'⟩
      · rw [cfgEPosts_label] at hE
        refine Program.Intercept.intro (Or.inl ⟨?_, l, ha.symm, hmem', ⟨hE, hst'⟩, ?_⟩)
        · show ¬ ((s.push64 ra).regs.get64 .rsp).SerialLt (u.data.regs.get64 .rsp)
          rw [hst'.1]
          exact BitVec.not_serialLt_self _
        · exact decreases_of_steps_lt abs fun _ =>
            steps_lt_of_error ablock next hl (by simp) hrun hfix
      · rw [cfgEPosts_exit] at hE
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

theorem wrp_cfg {p : Program} (next : CfgLabel → CfgLabel)
    (hnext : ∀ blk ∈ Program.blocks p, next blk.label = blk.next)
    {ablock : CfgLabel → BlockM Aσ Unit} {s : MachineData} {ra : Int64}
    (h : ∀ blk ∈ Program.blocks p, ∀ t, SameStackFrame (s.push64 ra) t →
      ⦃(· = t)⦄ blk.body ⪯[Concretization.ofStateRepr abs] (ablock blk.label)
        ⦃FallRel (s.push64 ra); JumpRel p (s.push64 ra)⦄) :
    wrp (Concretization.ofStateRepr abs) p (cfgLoop ablock next .entry) (fun _ _ => ⊤) (RetRel s ra)
      (s.push64 ra) :=
  wrp_cfg_le abs next hnext h (s.push64 ra) rfl

@[vcgen_simp] theorem Program.Block.label_mk (l : CfgLabel) (i : Nat) (b : Program) (n : CfgLabel) :
    (Program.Block.mk l i b n).label = l := rfl
@[vcgen_simp] theorem Program.Block.body_mk (l : CfgLabel) (i : Nat) (b : Program) (n : CfgLabel) :
    (Program.Block.mk l i b n).body = b := rfl
@[vcgen_simp] theorem Program.Block.next_mk (l : CfgLabel) (i : Nat) (b : Program) (n : CfgLabel) :
    (Program.Block.mk l i b n).next = n := rfl

attribute [vcgen_simp] Program.blocks_eq Program.view_cons_instr Program.view_cons_label
  Program.view_nil' Program.blocksFrom_cons Program.blocksFrom_nil

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

/-- The control-flow rule as a spec: the abstract program is `cfgLoop` over a table of blocks, one
cell per label, which `ascend` fills block by block. The program is embedded in the host, so its
labels are distinct and each block falls through to its successor in the text. -/
theorem refines_cfg {p : Program} [Embeds p] (tbl : Table CfgLabel (BlockM Aσ Unit))
    {s : MachineData} {ra : Int64}
    (h : ∀ blk ∈ Program.blocks p, ∀ t, SameStackFrame (s.push64 ra) t →
      ⦃(· = t)⦄ blk.body ⪯[Concretization.ofStateRepr abs] (Table.get tbl blk.label)
        ⦃FallRel (s.push64 ra); JumpRel p (s.push64 ra)⦄) :
    ⦃(· = s.push64 ra)⦄ p ⪯[Concretization.ofStateRepr abs]
      (cfgLoop (Table.get tbl) (Program.next p) .entry) ⦃fun _ _ => ⊤; RetRel s ra⦄ :=
  ⟨wrp_cfg_le abs (Program.next p)
    (fun _ hmem => Program.next_eq_of_nodup Program.labels_nodup_of_embeds hmem) h⟩

end

end Ascent.Kraken
