import Demo.Structure

/-!
# Loops of a block table

The rules of this file turn a block loop into a structured loop step by step, on the table. Each
rule takes as a premise the refinement of the cells it moves, with an exception relation that names
the labels a cell may jump to, so the run that applies the rule refines the cells and proves their
jump targets at once. `refines_cfgLoop_self` is the last step: a table of one cell that jumps only
to itself is a `repeat'` loop.
-/

open Std.WP Lean.Order Ascent

namespace Ascent.Kraken

section
variable {σ α : Type}

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

/-- The loop of a cell `ab` that jumps only to itself: the cell runs again on its jump and the loop
ends when the cell falls through. -/
noncomputable def selfLoop {σ : Type} (ab : BlockM σ Unit) : BlockM σ Unit :=
  FixLoop.mk.forIn PUnit.unit fun _ _ =>
    tryCatch (ab >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun _ => pure (ForInStep.yield PUnit.unit))

section
variable {Cσ Aσ : Type} (view : Cσ → Aσ)

theorem refines_cfgLoop_self {b : BlockM Cσ Unit} {ab : BlockM Aσ Unit} {L : Label}
    {next : CfgLabel → CfgLabel} {I : Cσ → Prop}
    (hb : ⦃I⦄ b ⪯[Concretization.ofStateRepr view] ab
      ⦃fun _ _ => I; (fun l l' t => l = .label L ∧ l' = l ∧ I t, estack⟨⟩)⦄)
    (hnext : next (.label L) = .exit) :
    ⦃I⦄ (cfgLoop (Table.get [(.label L, b)]) next (.label L)) ⪯[Concretization.ofStateRepr view]
      (selfLoop ab) ⦃fun _ _ => I; (fun l l' t => l = l' ∧ I t, estack⟨⟩)⦄ := by
  have hget : Table.get [(CfgLabel.label L, b)] (.label L) = b := by simp [Table.get, List.lookup]
  generalize htbl : Table.get [(CfgLabel.label L, b)] = tbl at hget ⊢
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred] at hs
  obtain ⟨hI, hw⟩ := hs
  unfold selfLoop at hw
  have := FixLoop.forIn_induct (m := BlockM Aσ) (β := PUnit)
    (fun _ _ => tryCatch (ab >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun _ => pure (ForInStep.yield PUnit.unit)))
    (fun g => ∀ s, I s → wp (g PUnit.unit) Qa Ea (view s) →
      wp (cfgLoop tbl next (.label L))
        ((Concretization.ofStateRepr view).post (fun _ _ => I) Qa)
        (EPostsConcretization.ePosts (Concretization.ofStateRepr view)
          (fun l l' t => l = l' ∧ I t, estack⟨⟩) Ea) s)
    (admissible_pi _ fun s => admissible_pi _ fun _ =>
      admissible_apply (fun _ u => wp u Qa Ea (view s) → _) PUnit.unit
        (admissible_wp_imp _ Ea (view s) _)) ?_
  · exact this s hI hw
  intro g ih s hI hw
  simp only [FixLoop.step, WPMonadExact.wp_bind_eq, wp_tryCatch_block, WPMonadExact.wp_pure_eq] at hw
  rw [wp_cfgLoop _ _ _ _ _ (by simp), hget, hnext, wp_cfgLoop_exit_fn]
  have hb' := wrp_transport hb.le_wrp (fun _ => Qa PUnit.unit)
    (fun _ m => wp (g PUnit.unit) Qa Ea m, Ea.2) s
    (by simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]; exact ⟨hI, hw⟩)
  refine WP.wp_monotone (x := b) ?_ ?_ s hb'
  · intro u t ht
    rw [Concretization.post_pi] at ht ⊢
    obtain ⟨_, hIt, hq⟩ := ht
    exact ⟨PUnit.unit, hIt, hq⟩
  · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l t ht
    rw [Concretization.post_pi] at ht
    obtain ⟨l', ⟨rfl, rfl, hIt⟩, hq⟩ := ht
    simp only [cfgEPosts, reduceCtorEq, ↓reduceIte]
    exact ih t hIt hq

end

/-! ## The jumps of a text

`Program.jumpLabel p l` is the target of the conditional jump of the block at `l` in the text `p`,
`.exit` for a block without one. `Program.isSelfLoop p l` holds when the block at `l` jumps to
itself. Both are functions of the literal text, so the simp step evaluates them. -/

/-- The target of a conditional jump. -/
def Directive.jumpTarget? : Directive → Option Label
  | .instr (.regular _ _ (.jcc _ l)) => some l
  | _ => none

/-- The jump target of the block at `l` among `bs`, `.exit` for a block without a jump. -/
def Program.jumpIn : List Program.Block → CfgLabel → CfgLabel
  | [], _ => .exit
  | blk :: bs, l =>
    if blk.label = l then
      match blk.body.findSome? Directive.jumpTarget? with
      | some j => .label j
      | none => .exit
    else Program.jumpIn bs l

def Program.jumpLabel (p : Program) (l : CfgLabel) : CfgLabel := Program.jumpIn (Program.blocks p) l

/-- The block at `l` jumps to itself. -/
def Program.isSelfLoop (p : Program) (l : CfgLabel) : Bool :=
  match l, Program.jumpLabel p l with
  | .label L, .label J => J == L
  | _, _ => false

@[vcgen_simp] theorem Program.jumpIn_nil (l : CfgLabel) : Program.jumpIn [] l = .exit := rfl
@[vcgen_simp] theorem Program.jumpIn_cons (blk : Program.Block) (bs : List Program.Block)
    (l : CfgLabel) :
    Program.jumpIn (blk :: bs) l = if blk.label = l then
      (match blk.body.findSome? Directive.jumpTarget? with
        | some j => .label j
        | none => .exit)
      else Program.jumpIn bs l := rfl
@[vcgen_simp] theorem Program.jumpLabel_eq (p : Program) (l : CfgLabel) :
    Program.jumpLabel p l = Program.jumpIn (Program.blocks p) l := rfl
attribute [vcgen_simp] Program.isSelfLoop Directive.jumpTarget? List.findSome?_cons
  List.findSome?_nil

/-! ## The structuring rules

The run turns a block loop into a structured program label by label. At each label `l` the marker
`loopAt (Program.isSelfLoop p l)` records whether the block at `l` jumps to itself; the simp step
evaluates it, and the literal selects the rule. A block that jumps to itself becomes a `selfLoop`
followed by the program at its fallthrough. Any other block runs once inside `tryCatch` and
continues at its jump target or at its fallthrough. Every value that selects a rule enters a premise
as an equation in a binder, `∀ b, b = Program.isSelfLoop p l → …`: the simp step evaluates the right
side, and the run substitutes the literal for `b`. -/

/-- The block loop at `l`, marked with whether the block at `l` jumps to itself. -/
def loopAt {σ : Type} (_self : Bool) (ablock : CfgLabel → BlockM σ Unit) (next : CfgLabel → CfgLabel)
    (l : CfgLabel) : BlockM σ Unit :=
  cfgLoop ablock next l

theorem wp_throw_block {σ α : Type} (l : CfgLabel) (Q : α → σ → Prop)
    (E : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (throw l : BlockM σ α) Q E s = E.1 l s := by
  rw [wp_BlockM_eq]
  rfl

section
variable {Cσ Aσ : Type} {view : Cσ → Aσ} {I : Cσ → Prop} {Q : Unit → Unit → Cσ → Prop}
  {E : (CfgLabel → CfgLabel → Cσ → Prop) × EStack⟨⟩}

theorem refines_cfgLoop_text {ablock : CfgLabel → BlockM Cσ Unit} {p : Program} {l : CfgLabel}
    {a : BlockM Aσ Unit}
    (h : ∀ b, b = Program.isSelfLoop p l → ⦃I⦄ (loopAt b ablock (Program.next p) l)
      ⪯[Concretization.ofStateRepr view] a ⦃Q; E⦄) :
    ⦃I⦄ (cfgLoop ablock (Program.next p) l) ⪯[Concretization.ofStateRepr view] a ⦃Q; E⦄ :=
  h _ rfl

theorem refines_loopAt_exit {b : Bool} {ablock : CfgLabel → BlockM Cσ Unit}
    {next : CfgLabel → CfgLabel} (hQ : ∀ t, I t → Q () () t) :
    ⦃I⦄ (loopAt b ablock next .exit) ⪯[Concretization.ofStateRepr view] (pure () : BlockM Aσ Unit)
      ⦃Q; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred,
    WPMonadExact.wp_pure_eq] at hs
  show wp (cfgLoop ablock next .exit) _ _ s
  rw [wp_cfgLoop_exit, Concretization.post_pi]
  exact ⟨(), hQ s hs.1, hs.2⟩

theorem refines_loopAt_step {ablock : CfgLabel → BlockM Cσ Unit} {p : Program} {l : CfgLabel}
    {ac aJ aN : BlockM Aσ Unit} (hl : l ≠ .exit)
    (hc : ∀ c, c = ablock l → ⦃I⦄ c ⪯[Concretization.ofStateRepr view] ac
      ⦃fun _ _ => I; (fun l₁ l₂ t => l₂ = l₁ ∧ ((l₁ = Program.jumpLabel p l ∧ l₁ ≠ .exit ∧ I t)
        ∨ (l₁ = .exit ∧ E.1 .exit .exit t)), estack⟨⟩)⦄)
    (hJ : ∀ j, j = Program.jumpLabel p l → ∀ b, b = Program.isSelfLoop p j →
      ⦃I⦄ (loopAt b ablock (Program.next p) j) ⪯[Concretization.ofStateRepr view] aJ ⦃Q; E⦄)
    (hN : ∀ n, n = Program.next p l → ∀ b, b = Program.isSelfLoop p n →
      ⦃I⦄ (loopAt b ablock (Program.next p) n) ⪯[Concretization.ofStateRepr view] aN ⦃Q; E⦄) :
    ⦃I⦄ (loopAt false ablock (Program.next p) l) ⪯[Concretization.ofStateRepr view]
      (do
        let j ← tryCatch (ac >>= fun _ => pure false)
          (fun (l' : CfgLabel) => if l' = CfgLabel.exit then throw CfgLabel.exit else pure true)
        if j then aJ else aN)
      ⦃Q; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred] at hs
  obtain ⟨hI, hw⟩ := hs
  simp only [WPMonadExact.wp_bind_eq, wp_tryCatch_block, WPMonadExact.wp_pure_eq,
    Bool.false_eq_true, ↓reduceIte] at hw
  show wp (cfgLoop ablock (Program.next p) l) _ _ s
  rw [wp_cfgLoop _ _ _ _ _ hl]
  have hb := wrp_transport (hc _ rfl).le_wrp (fun _ m => wp aN Qa Ea m)
    (fun l' m => if l' = .exit then Ea.1 .exit m else wp aJ Qa Ea m, Ea.2) s
    (by
      simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]
      refine ⟨hI, ?_⟩
      refine WP.wp_monotone (x := ac) PartialOrder.rel_refl ?_ (view s) hw
      refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l' m hm
      by_cases hx : l' = .exit
      · simp only [hx, ↓reduceIte] at hm ⊢
        exact hm
      · simp only [hx, ↓reduceIte] at hm ⊢
        exact hm)
  refine WP.wp_monotone (x := ablock l) ?_ ?_ s hb
  · intro _ t ht
    rw [Concretization.post_pi] at ht
    obtain ⟨_, hIt, hq⟩ := ht
    exact wrp_transport (hN _ rfl _ rfl).le_wrp Qa Ea t
      (by simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]; exact ⟨hIt, hq⟩)
  · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l₁ t ht
    rw [Concretization.post_pi] at ht
    obtain ⟨l₂, ⟨rfl, hrel⟩, hq⟩ := ht
    rcases hrel with ⟨hJ', hne, hIt⟩ | ⟨rfl, hE⟩
    · simp only [hne, ↓reduceIte] at hq
      simp only [cfgEPosts, hne, ↓reduceIte]
      subst hJ'
      exact wrp_transport (hJ _ rfl _ rfl).le_wrp Qa Ea t
        (by simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]; exact ⟨hIt, hq⟩)
    · simp only [↓reduceIte] at hq
      simp only [cfgEPosts, ↓reduceIte, EPostsConcretization.ePosts_cons]
      rw [Concretization.post_pi]
      exact ⟨.exit, hE, hq⟩

theorem refines_loopAt_self {ablock : CfgLabel → BlockM Cσ Unit} {p : Program} {L : Label}
    {ab aN : BlockM Aσ Unit}
    (hb : ∀ c, c = ablock (.label L) → ⦃I⦄ c ⪯[Concretization.ofStateRepr view] ab
      ⦃fun _ _ => I; (fun l₁ l₂ t => l₁ = .label L ∧ l₂ = l₁ ∧ I t, estack⟨⟩)⦄)
    (hN : ∀ n, n = Program.next p (.label L) → ∀ b, b = Program.isSelfLoop p n →
      ⦃I⦄ (loopAt b ablock (Program.next p) n) ⪯[Concretization.ofStateRepr view] aN ⦃Q; E⦄) :
    ⦃I⦄ (loopAt true ablock (Program.next p) (.label L)) ⪯[Concretization.ofStateRepr view]
      (selfLoop ab >>= fun _ => aN) ⦃Q; E⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred,
    WPMonadExact.wp_bind_eq] at hs
  obtain ⟨hI, hw⟩ := hs
  unfold selfLoop at hw
  show wp (cfgLoop ablock (Program.next p) (.label L)) _ _ s
  have := FixLoop.forIn_induct (m := BlockM Aσ) (β := PUnit)
    (fun _ _ => tryCatch (ab >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun _ => pure (ForInStep.yield PUnit.unit)))
    (fun g => ∀ s, I s → wp (g PUnit.unit) (fun _ => wp aN Qa Ea) Ea (view s) →
      wp (cfgLoop ablock (Program.next p) (.label L))
        ((Concretization.ofStateRepr view).post Q Qa)
        (EPostsConcretization.ePosts (Concretization.ofStateRepr view) E Ea) s)
    (admissible_pi _ fun s => admissible_pi _ fun _ =>
      admissible_apply (fun _ u => wp u (fun _ => wp aN Qa Ea) Ea (view s) → _) PUnit.unit
        (admissible_wp_imp _ Ea (view s) _)) ?_
  · exact this s hI hw
  intro g ih s hI hw
  simp only [FixLoop.step, WPMonadExact.wp_bind_eq, wp_tryCatch_block, WPMonadExact.wp_pure_eq] at hw
  rw [wp_cfgLoop _ _ _ _ _ (by simp)]
  have hb' := wrp_transport (hb _ rfl).le_wrp (fun _ m => wp aN Qa Ea m)
    (fun _ m => wp (g PUnit.unit) (fun _ => wp aN Qa Ea) Ea m, Ea.2) s
    (by simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]; exact ⟨hI, hw⟩)
  refine WP.wp_monotone (x := ablock (.label L)) ?_ ?_ s hb'
  · intro _ t ht
    rw [Concretization.post_pi] at ht
    obtain ⟨_, hIt, hq⟩ := ht
    exact wrp_transport (hN _ rfl _ rfl).le_wrp Qa Ea t
      (by simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]; exact ⟨hIt, hq⟩)
  · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l t ht
    rw [Concretization.post_pi] at ht
    obtain ⟨l', ⟨rfl, rfl, hIt⟩, hq⟩ := ht
    simp only [cfgEPosts, reduceCtorEq, ↓reduceIte]
    exact ih t hIt hq

end

end Ascent.Kraken
