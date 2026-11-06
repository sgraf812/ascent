import Demo.Loops

/-!
# Structuring a block loop by rewriting

`cfgLoop_eq_loop` unfolds the block loop at a label `l` into a `repeat'` loop: the cell at `l`
runs inside `try`, a jump back to `l` continues the loop, and every other exit leaves it with the
rest of the program. Pushing the `try` into the cell with the `tryCatch` equations of this file
and deciding the literal labels then structures the program, and a loop whose body never
continues collapses to its body.
-/

open Std.WP Lean.Order Ascent

namespace Ascent.Kraken

section
variable {σ α : Type}

theorem BlockM.ext_wp {x y : BlockM σ α}
    (h : ∀ (Q : α → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩) s, wp x Q E s → wp y Q E s)
    (h' : ∀ (Q : α → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩) s, wp y Q E s → wp x Q E s) :
    x = y := by
  have key : ∀ (u v : BlockM σ α) s,
      (∀ (Q : α → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩), wp u Q E s → wp v Q E s) →
      ∀ r, u.run.run s = some r → v.run.run s = some r := by
    intro u v s huv r hr
    have := huv (fun a st => (some (.ok a, st) : UB _) = some r)
      (fun e st => (some (.error e, st) : UB _) = some r, estack⟨⟩)
    rw [wp_BlockM_eq, wp_BlockM_eq, hr] at this
    rcases r with ⟨_ | _, _⟩ <;>
    · specialize this rfl
      revert this
      rcases v.run.run s with _ | ⟨_ | _, _⟩ <;> simp <;> rintro rfl rfl <;> rfl
  apply ExceptT.ext
  apply StateT.ext
  intro s
  show x.run.run s = y.run.run s
  rcases hx : x.run.run s with _ | r
  · rcases hy : y.run.run s with _ | r
    · rfl
    · rw [key y x s (fun Q E => h' Q E s) r hy] at hx
      exact (nomatch hx)
  · exact (key x y s (fun Q E => h Q E s) r hx).symm

end

section
variable {σ : Type} (ablock : CfgLabel → BlockM σ Unit) (next : CfgLabel → CfgLabel)

def cfgStep (f : CfgLabel → BlockM σ Unit) (l : CfgLabel) : BlockM σ Unit :=
  show σ → UB (Except CfgLabel Unit × σ) from fun s =>
    if l = .exit then pure (Except.ok (), s) else do
      let p ← (ExceptT.run (ablock l)).run s
      match p.fst with
      | Except.ok _ => (f (next l)).run.run p.snd
      | Except.error l' =>
        if l' = .exit then pure (Except.error .exit, p.snd) else (f l').run.run p.snd

theorem cfgStep_run_of_ne (f : CfgLabel → BlockM σ Unit) {l : CfgLabel} (hl : l ≠ .exit) (s : σ) :
    (cfgStep ablock next f l).run.run s = ((ablock l).run.run s >>= fun p =>
      match p.fst with
      | Except.ok _ => (f (next l)).run.run p.snd
      | Except.error l' =>
        if l' = .exit then pure (Except.error .exit, p.snd) else (f l').run.run p.snd) := by
  show (if l = .exit then _ else _) = _
  rw [if_neg hl]

theorem cfgStep_exit (f : CfgLabel → BlockM σ Unit) : cfgStep ablock next f .exit = pure () := rfl

theorem cfgLoop_induct (motive : (CfgLabel → BlockM σ Unit) → Prop) (hadm : admissible motive)
    (h : ∀ f, motive f → motive (cfgStep ablock next f)) : motive (cfgLoop ablock next) :=
  cfgFix.fixpoint_induct ablock next motive hadm h

theorem wp_cfgStep (f : CfgLabel → BlockM σ Unit) {l : CfgLabel} (hl : l ≠ .exit)
    (Qa : Unit → σ → Prop) (Ea : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ) :
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
  show (cfgFix ablock next l : σ → UB (Except CfgLabel Unit × σ)) = cfgStep ablock next _ l
  funext s
  rw [cfgFix]
  rfl

theorem admissible_wp_imp_fn (P : CfgLabel → (Unit → σ → Prop) → ((CfgLabel → σ → Prop) × EStack⟨⟩) → σ → Prop) :
    admissible fun f : CfgLabel → BlockM σ Unit => ∀ l Qa Ea s, wp (f l) Qa Ea s → P l Qa Ea s :=
  admissible_pi _ fun l => admissible_pi _ fun Qa => admissible_pi _ fun Ea => admissible_pi _ fun s =>
    admissible_apply (fun _ u => wp u Qa Ea s → P l Qa Ea s) l (admissible_wp_imp _ Ea s _)

theorem wp_cfgLoop_epost {l : CfgLabel} {Qa : Unit → σ → Prop} {Ea Ea' : (CfgLabel → σ → Prop) × EStack⟨⟩}
    (hE : ∀ s, Ea.1 .exit s → Ea'.1 .exit s) {s : σ} :
    wp (cfgLoop ablock next l) Qa Ea s → wp (cfgLoop ablock next l) Qa Ea' s := by
  have := cfgLoop_induct ablock next
    (fun f => ∀ l Qa s, wp (f l) Qa Ea s → wp (cfgLoop ablock next l) Qa Ea' s)
    (admissible_pi _ fun l => admissible_pi _ fun Qa => admissible_pi _ fun s =>
      admissible_apply (fun _ u => wp u Qa Ea s → _) l (admissible_wp_imp _ Ea s _)) ?_
  · exact this l Qa s
  intro f ih l Qa s hw
  by_cases hl : l = .exit
  · subst hl
    rw [cfgStep_exit] at hw
    rw [cfgLoop_eq_cfgStep, cfgStep_exit]
    exact hw
  rw [wp_cfgStep _ _ _ hl] at hw
  rw [cfgLoop_eq_cfgStep, wp_cfgStep _ _ _ hl]
  refine WP.wp_monotone (x := ablock l) (fun _ t ht => ih _ _ t ht) ?_ s hw
  refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
  intro l' t ht
  by_cases h : l' = .exit
  · subst h; simp only [↓reduceIte] at ht ⊢; exact hE t ht
  · simp only [h, ↓reduceIte] at ht ⊢; exact ih _ _ t ht

theorem wp_cfgStep_imp (f : CfgLabel → BlockM σ Unit)
    (ih : ∀ l Qa Ea s, wp (f l) Qa Ea s → wp (cfgLoop ablock next l) Qa Ea s) :
    ∀ l Qa Ea s, wp (cfgStep ablock next f l) Qa Ea s → wp (cfgLoop ablock next l) Qa Ea s := by
  intro l Qa Ea s hw
  by_cases hl : l = .exit
  · subst hl
    rw [cfgStep_exit] at hw
    rw [cfgLoop_eq_cfgStep, cfgStep_exit]
    exact hw
  rw [wp_cfgStep _ _ _ hl] at hw
  rw [cfgLoop_eq_cfgStep, wp_cfgStep _ _ _ hl]
  refine WP.wp_monotone (x := ablock l) (fun _ t ht => ih _ _ _ t ht) ?_ s hw
  refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
  intro l' t ht
  by_cases h : l' = .exit
  · subst h; simp only [↓reduceIte] at ht ⊢; exact ht
  · simp only [h, ↓reduceIte] at ht ⊢; exact ih _ _ _ t ht

def loopBody (l : CfgLabel) (_ : Unit) (_ : PUnit) : BlockM σ (ForInStep PUnit) :=
  tryCatch (ablock l >>= fun _ => cfgLoop ablock next (next l) >>= fun _ =>
      pure (ForInStep.done PUnit.unit))
    (fun l' => if l' = l then pure (ForInStep.yield PUnit.unit)
      else if l' = .exit then throw .exit
      else cfgLoop ablock next l' >>= fun _ => pure (ForInStep.done PUnit.unit))

theorem wp_loopBody {l : CfgLabel} (hl : l ≠ .exit) (R : ForInStep PUnit → σ → Prop)
    (E : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (loopBody ablock next l () PUnit.unit) R E s
      = wp (ablock l) (fun _ => wp (cfgLoop ablock next (next l)) (fun _ => R (.done PUnit.unit)) E)
          (fun l' => if l' = l then R (.yield PUnit.unit)
            else if l' = .exit then E.1 .exit
            else wp (cfgLoop ablock next l') (fun _ => R (.done PUnit.unit)) E, E.2) s := by
  have hle : CfgLabel.exit ≠ l := fun h => hl h.symm
  rw [loopBody, wp_tryCatch_block, WPMonadExact.wp_bind_eq]
  have key : ∀ {P P' : Unit → σ → Prop} {F F' : (CfgLabel → σ → Prop) × EStack⟨⟩},
      P = P' → F = F' → wp (ablock l) P F s = wp (ablock l) P' F' s := fun h1 h2 => h1 ▸ h2 ▸ rfl
  refine key ?_ ?_
  · funext _ t
    simp only [WPMonadExact.wp_bind_eq, WPMonadExact.wp_pure_eq]
    apply propext
    constructor
    all_goals
      refine wp_cfgLoop_epost ablock next ?_
      intro t' h'
      simp only [hle, ↓reduceIte, wp_throw_block] at h' ⊢
      exact h'
  · refine Prod.ext ?_ rfl
    funext l' t
    by_cases h1 : l' = l
    · subst h1; simp only [↓reduceIte, WPMonadExact.wp_pure_eq]
    by_cases h2 : l' = .exit
    · subst h2; simp only [h1, ↓reduceIte, wp_throw_block]
    simp only [h1, h2, ↓reduceIte, WPMonadExact.wp_bind_eq, WPMonadExact.wp_pure_eq]

theorem wp_cfgLoop_imp_loop {l : CfgLabel} (hl : l ≠ .exit) (Q : Unit → σ → Prop)
    (E : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (cfgLoop ablock next l) Q E s → wp (FixLoop.mk.forIn PUnit.unit (loopBody ablock next l)) Q E s := by
  have := cfgLoop_induct ablock next
    (fun f => (∀ l Qa Ea s, wp (f l) Qa Ea s → wp (cfgLoop ablock next l) Qa Ea s) ∧
      ∀ (Q : Unit → σ → Prop) E s, wp (f l) Q E s →
        wp (FixLoop.mk.forIn PUnit.unit (loopBody ablock next l)) Q E s)
    (admissible_and _ _ (admissible_wp_imp_fn _)
      (admissible_pi _ fun Q => admissible_pi _ fun E => admissible_pi _ fun s =>
        admissible_apply (fun _ u => wp u Q E s → _) l (admissible_wp_imp _ E s _)))
  refine (this ?_).2 Q E s
  intro f ⟨ih1, ih2⟩
  refine ⟨wp_cfgStep_imp ablock next f ih1, ?_⟩
  intro Q E s hw
  rw [wp_cfgStep _ _ _ hl] at hw
  rw [FixLoop.wp_forIn_eq, wp_loopBody _ _ hl]
  refine WP.wp_monotone (x := ablock l) (fun _ t ht => ih1 _ _ _ t ht) ?_ s hw
  refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
  intro l' t ht
  by_cases h1 : l' = l
  · subst h1
    simp only [hl, ↓reduceIte] at ht ⊢
    exact ih2 Q E t ht
  by_cases h2 : l' = .exit
  · subst h2; simp only [h1, ↓reduceIte] at ht ⊢; exact ht
  simp only [h1, h2, ↓reduceIte] at ht ⊢
  exact ih1 _ _ _ t ht

theorem wp_loop_imp_cfgLoop {l : CfgLabel} (hl : l ≠ .exit) (Q : Unit → σ → Prop)
    (E : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (FixLoop.mk.forIn PUnit.unit (loopBody ablock next l)) Q E s → wp (cfgLoop ablock next l) Q E s := by
  have := FixLoop.forIn_induct (m := BlockM σ) (β := PUnit) (loopBody ablock next l)
    (fun g => ∀ (Q : Unit → σ → Prop) E s, wp (g PUnit.unit) Q E s →
      wp (cfgLoop ablock next l) Q E s)
    (admissible_pi _ fun Q => admissible_pi _ fun E => admissible_pi _ fun s =>
      admissible_apply (fun _ u => wp u Q E s → _) PUnit.unit (admissible_wp_imp _ E s _))
  refine this ?_ Q E s
  intro g ih Q E s hw
  rw [FixLoop.step, WPMonadExact.wp_bind_eq, wp_loopBody _ _ hl] at hw
  simp only [WPMonadExact.wp_pure_eq] at hw
  rw [cfgLoop_eq_cfgStep, wp_cfgStep _ _ _ hl]
  refine WP.wp_monotone (x := ablock l) (fun _ t ht => ht) ?_ s hw
  refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
  intro l' t ht
  by_cases h1 : l' = l
  · subst h1
    simp only [hl, ↓reduceIte] at ht ⊢
    exact ih Q E t ht
  by_cases h2 : l' = .exit
  · subst h2; simp only [h1, ↓reduceIte] at ht ⊢; exact ht
  simp only [h1, h2, ↓reduceIte] at ht ⊢
  exact ht

theorem cfgLoop_eq_loop {l : CfgLabel} (hl : l ≠ .exit) :
    cfgLoop ablock next l = FixLoop.mk.forIn PUnit.unit (loopBody ablock next l) :=
  BlockM.ext_wp (wp_cfgLoop_imp_loop ablock next hl) (wp_loop_imp_cfgLoop ablock next hl)

theorem cfgLoop_label (L : Label) :
    cfgLoop ablock next (.label L) = FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (ablock (.label L) >>= fun _ => cfgLoop ablock next (next (.label L)) >>= fun _ =>
          pure (ForInStep.done PUnit.unit))
        (fun l' => if l' = .label L then pure (ForInStep.yield PUnit.unit)
          else if l' = .exit then throw .exit
          else cfgLoop ablock next l' >>= fun _ => pure (ForInStep.done PUnit.unit))) :=
  cfgLoop_eq_loop ablock next (l := .label L) (by simp)

theorem cfgLoop_entry :
    cfgLoop ablock next .entry = FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (ablock .entry >>= fun _ => cfgLoop ablock next (next .entry) >>= fun _ =>
          pure (ForInStep.done PUnit.unit))
        (fun l' => if l' = .entry then pure (ForInStep.yield PUnit.unit)
          else if l' = .exit then throw .exit
          else cfgLoop ablock next l' >>= fun _ => pure (ForInStep.done PUnit.unit))) :=
  cfgLoop_eq_loop ablock next (l := .entry) (by simp)

theorem cfgLoop_exit : cfgLoop ablock next .exit = pure () := by
  rw [cfgLoop_eq_cfgStep, cfgStep_exit]

theorem tryCatch_cfgLoop_bind {β : Type} (l : CfgLabel) (k : Unit → BlockM σ β)
    (h : CfgLabel → BlockM σ β) (hh : h .exit = throw .exit) :
    tryCatch (cfgLoop ablock next l >>= k) h = cfgLoop ablock next l >>= fun a => tryCatch (k a) h := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    have hf : ∀ a, wp (tryCatch (k a) h) Q E = wp (k a) Q (fun l => wp (h l) Q E, E.2) :=
      fun a => funext (wp_tryCatch_block _ _ _ _) <;>
    simp only [wp_tryCatch_block, WPMonadExact.wp_bind_eq, hf] <;>
    refine wp_cfgLoop_epost ablock next ?_ <;> intro t ht <;> simp only [hh, wp_throw_block] at ht ⊢ <;>
    exact ht

end

/-! ## Pushing `try` into a block -/

section
variable {σ β : Type}

theorem tryCatch_bind_assoc {α γ : Type} (x : BlockM σ α) (f : α → BlockM σ γ) (k : γ → BlockM σ β)
    (h : CfgLabel → BlockM σ β) :
    tryCatch ((x >>= f) >>= k) h = tryCatch (x >>= fun a => f a >>= k) h := by
  rw [bind_assoc]

theorem tryCatch_pure_bind {α : Type} (a : α) (k : α → BlockM σ β) (h : CfgLabel → BlockM σ β) :
    tryCatch (pure a >>= k) h = tryCatch (k a) h := by
  rw [pure_bind]

theorem tryCatch_pure (b : β) (h : CfgLabel → BlockM σ β) : tryCatch (pure b : BlockM σ β) h = pure b := by
  apply BlockM.ext_wp <;> intro Q E s <;> simp only [wp_tryCatch_block, WPMonadExact.wp_pure_eq] <;>
    exact id

theorem tryCatch_throw (l : CfgLabel) (h : CfgLabel → BlockM σ β) :
    tryCatch (throw l : BlockM σ β) h = h l := by
  apply BlockM.ext_wp <;> intro Q E s <;> simp only [wp_tryCatch_block, wp_throw_block] <;> exact id

theorem tryCatch_modifyIf_bind (g : σ → Prop) (f : σ → σ) (k : Unit → BlockM σ β)
    (h : CfgLabel → BlockM σ β) :
    tryCatch (AInstr.modifyIf g f >>= k) h = AInstr.modifyIf g f >>= fun a => tryCatch (k a) h := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [wp_tryCatch_block, WPMonadExact.wp_bind_eq, AInstr.wp_modifyIf] <;> exact id

def condState (c : σ → Bool) (x y : BlockM σ β) : BlockM σ β :=
  get >>= fun st => if c st then x else y

theorem wp_condState (c : σ → Bool) (x y : BlockM σ β) (Q : β → σ → Prop)
    (E : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (condState c x y) Q E s = if c s then wp x Q E s else wp y Q E s := by
  rw [condState, wp_get_bind]
  split <;> rfl

theorem tryCatch_branch_bind (c : σ → Bool) (l : CfgLabel) (k : Unit → BlockM σ β)
    (h : CfgLabel → BlockM σ β) :
    tryCatch (AInstr.branch c l >>= k) h = condState c (h l) (tryCatch (k ()) h) := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [wp_tryCatch_block, WPMonadExact.wp_bind_eq, AInstr.wp_branch, wp_condState] <;>
    split <;> exact id

def toDone (x : BlockM σ PUnit) : BlockM σ (ForInStep PUnit) :=
  x >>= fun _ => pure (ForInStep.done PUnit.unit)

theorem pure_done_eq : (pure (ForInStep.done PUnit.unit) : BlockM σ (ForInStep PUnit)) = toDone (pure ()) := by
  rw [toDone, pure_bind]

theorem throw_eq_toDone (l : CfgLabel) : (throw l : BlockM σ (ForInStep PUnit)) = toDone (throw l) := by
  apply BlockM.ext_wp <;> intro Q E s <;> simp only [toDone, WPMonadExact.wp_bind_eq, wp_throw_block] <;>
    exact id

theorem bind_toDone {α : Type} (x : BlockM σ α) (y : BlockM σ PUnit) :
    (x >>= fun _ => toDone y) = toDone (x >>= fun _ => y) := by
  simp only [toDone, bind_assoc]

theorem condState_toDone (c : σ → Bool) (x y : BlockM σ PUnit) :
    condState c (toDone x) (toDone y) = toDone (condState c x y) := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [toDone, WPMonadExact.wp_bind_eq, wp_condState] <;> split <;> exact id

theorem forIn_toDone (x : BlockM σ PUnit) :
    FixLoop.mk.forIn PUnit.unit (fun _ _ => toDone x) = x := by
  rw [FixLoop.forIn_eq, toDone, bind_assoc]
  simp only [pure_bind]
  exact bind_pure_unit

end

/-! ## Deciding labels and tables -/

theorem Table.get_cons {κ β : Type} [DecidableEq κ] [Inhabited β] (k k' : κ) (b : β)
    (t : Table κ β) : Table.get ((k', b) :: t) k = if k = k' then b else Table.get t k := by
  simp only [Table.get, List.lookup]
  by_cases h : k = k'
  · simp [h]
  · have hb : (k == k') = false := by simpa using h
    simp [h, hb]

theorem CfgLabel.label_eq_label (a b : Label) : (CfgLabel.label a = CfgLabel.label b) = (@Eq String a b) := by
  simp

theorem CfgLabel.label_eq_exit (a : Label) : (CfgLabel.label a = .exit) = False := by simp
theorem CfgLabel.exit_eq_label (a : Label) : (CfgLabel.exit = .label a) = False := by simp
theorem CfgLabel.label_eq_entry (a : Label) : (CfgLabel.label a = .entry) = False := by simp
theorem CfgLabel.entry_eq_label (a : Label) : (CfgLabel.entry = .label a) = False := by simp
theorem CfgLabel.entry_eq_exit : (CfgLabel.entry = .exit) = False := by simp
theorem CfgLabel.exit_eq_entry : (CfgLabel.exit = .entry) = False := by simp
theorem CfgLabel.eq_self (l : CfgLabel) : (l = l) = True := by simp

/-! ## The steps of the example -/

namespace AInstr
variable {β : Type} (k : Unit → BlockM MachineData β) (h : CfgLabel → BlockM MachineData β)

theorem tryCatch_movRegSib8_bind (r b i : Reg64) (d : Int64) :
    tryCatch (movRegSib8 r b i d >>= k) h = movRegSib8 r b i d >>= fun a => tryCatch (k a) h :=
  tryCatch_modifyIf_bind _ _ k h
theorem tryCatch_addRegSib8_bind (rd b i : Reg64) (d : Int64) :
    tryCatch (addRegSib8 rd b i d >>= k) h = addRegSib8 rd b i d >>= fun a => tryCatch (k a) h :=
  tryCatch_modifyIf_bind _ _ k h
theorem tryCatch_movSib8Reg_bind (b i : Reg64) (d : Int64) (rs : Reg64) :
    tryCatch (movSib8Reg b i d rs >>= k) h = movSib8Reg b i d rs >>= fun a => tryCatch (k a) h :=
  tryCatch_modifyIf_bind _ _ k h
theorem tryCatch_incReg_bind (r : Reg64) :
    tryCatch (incReg r >>= k) h = incReg r >>= fun a => tryCatch (k a) h :=
  tryCatch_modifyIf_bind _ _ k h
theorem tryCatch_xorReg32Reg32_bind (rd rs : Reg64) :
    tryCatch (xorReg32Reg32 rd rs >>= k) h = xorReg32Reg32 rd rs >>= fun a => tryCatch (k a) h :=
  tryCatch_modifyIf_bind _ _ k h
theorem tryCatch_cmpJcc_bind (ra rb : Reg64) (cc : CondCode) (l : Label) :
    tryCatch (cmpJcc ra rb cc l >>= k) h
      = condState (fun st => cc.cmp (st.regs.get64 ra) (st.regs.get64 rb)) (h (.label l))
          (tryCatch (k ()) h) :=
  tryCatch_branch_bind _ _ k h
theorem tryCatch_testJcc_bind (ra rb : Reg64) (cc : CondCode) (l : Label) :
    tryCatch (testJcc ra rb cc l >>= k) h
      = condState (fun st => cc.cmp (st.regs.get64 ra &&& st.regs.get64 rb) 0) (h (.label l))
          (tryCatch (k ()) h) :=
  tryCatch_branch_bind _ _ k h

theorem tryCatch_ret_bind (hh : h .exit = throw .exit) : tryCatch (ret >>= k) h = ret >>= k := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [wp_tryCatch_block, WPMonadExact.wp_bind_eq, ret, wp_exitIf, hh, wp_throw_block] <;>
    exact id

end AInstr

theorem tryCatch_table_get_bind {σ α β : Type} [Inhabited (BlockM σ α)] (k k' : CfgLabel) (c : BlockM σ α)
    (t : Table CfgLabel (BlockM σ α)) (K : α → BlockM σ β) (h : CfgLabel → BlockM σ β) :
    tryCatch (Table.get ((k', c) :: t) k >>= K) h
      = if k = k' then tryCatch (c >>= K) h else tryCatch (Table.get t k >>= K) h := by
  rw [Table.get_cons]
  split <;> rfl

end Ascent.Kraken
