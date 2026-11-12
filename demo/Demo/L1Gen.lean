import Demo.L1

/-!
# The first layer under a memory relation

The rules of `Demo.L1` relate a concrete state `s` to the abstract state `abs s`. This file states
them for `JRel M`, which relates `s` to every abstract state `a` with the registers, the vector
registers and the cleared flags of `abs s`, and a memory related to the memory of `s` by `M`.
`M = Eq` gives `abs s` itself, and `M = Mem.Sub` gives every abstract state that forgets memory.

`MonoRun M x` states that the abstract program `x` runs on related states to related states with
the same result. A rule of `Demo.L1` whose abstract program is monotone holds for every `JRel M`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRel ofStateRepr_pred ofStateRel_pred)
open scoped Program.WP

namespace Ascent.Kraken

/-! ## Monotone abstract programs -/

/-- `x` runs on related states to related states with the same result. -/
def MonoRun (M : DataMem → DataMem → Prop) {α : Type} (x : BlockM MachineData α) : Prop :=
  ∀ a b, StRel M a b → ∀ r, x.run.run a = some r →
    ∃ r', x.run.run b = some r' ∧ r.1 = r'.1 ∧ StRel M r.2 r'.2

section
variable {M : DataMem → DataMem → Prop}

theorem MonoRun.wp {α : Type} {x : BlockM MachineData α} (hx : MonoRun M x) {a b : MachineData}
    (hab : StRel M a b) {Q : α → MachineData → Prop} {E : (Int64 → MachineData → Prop) × EStack⟨⟩}
    (h : wp x Q E a) :
    wp x (fun v b' => ∃ a', StRel M a' b' ∧ Q v a') (fun l b' => ∃ a', StRel M a' b' ∧ E.1 l a', E.2) b := by
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

/-- A refinement under `ofStateRepr abs` with a monotone abstract program holds under every
`JRel M`. -/
theorem wrp_rel_of_abs {CProg : Type} {CVal AV : Type}
    [WP CProg CVal (MachineData → Prop) (Int64 → MachineData → Prop)]
    {c : CProg} {x : BlockM MachineData AV} {P : MachineData → Prop}
    {Q : CVal → AV → MachineData → Prop} {E : Int64 → Int64 → MachineData → Prop}
    (hx : MonoRun M x) (h : P ⊑ wrp (ofStateRepr abs) c x Q E) :
    P ⊑ wrp (ofStateRel (JRel M)) c x Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred] at ht
  obtain ⟨hP, a, hJ, ha⟩ := ht
  have hb := hx.wp hJ ha
  have hc := wrp_transport h (fun v b' => ∃ a', StRel M a' b' ∧ Qa v a')
    (fun l b' => ∃ a', StRel M a' b' ∧ Ea.1 l a', Ea.2) t
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

end

/-! ## The step vocabulary is monotone -/

/-- `f` reads only the registers and the flags. -/
def RegFn {β : Type} (f : MachineData → β) : Prop :=
  ∀ a b : MachineData, a.regs = b.regs → a.status = b.status → f a = f b

section
variable {M : DataMem → DataMem → Prop}

theorem StRel.regs {a b : MachineData} (h : StRel M a b) : a.regs = b.regs := h.1
theorem StRel.status {a b : MachineData} (h : StRel M a b) : a.status = b.status := h.2.2.1
theorem StRel.mem {a b : MachineData} (h : StRel M a b) : M a.dmem b.dmem := h.2.2.2

theorem RegFn.eq {β : Type} {f : MachineData → β} (hf : RegFn f) {a b : MachineData} (h : StRel M a b) :
    f a = f b := hf a b h.regs h.status

theorem monoRun_pure {α : Type} (v : α) : MonoRun M (pure v : BlockM MachineData α) :=
  fun a b hab r hr => ⟨(.ok v, b), rfl, by cases hr; rfl, by cases hr; exact hab⟩

theorem monoRun_throw {α : Type} (l : Int64) : MonoRun M (throw l : BlockM MachineData α) :=
  fun a b hab r hr => ⟨(.error l, b), rfl, by cases hr; rfl, by cases hr; exact hab⟩

theorem monoRun_bind {α β : Type} {x : BlockM MachineData α} {k : α → BlockM MachineData β}
    (hx : MonoRun M x) (hk : ∀ v, MonoRun M (k v)) : MonoRun M (x >>= k) := by
  intro a b hab r hr
  rw [BlockM.run_bind] at hr ⊢
  cases hxa : x.run.run a with
  | none => rw [hxa] at hr; exact nomatch hr
  | some p =>
    rw [hxa] at hr
    obtain ⟨p', hxb, h1, h2⟩ := hx a b hab p hxa
    rw [hxb]
    obtain ⟨e, s⟩ := p
    obtain ⟨e', s'⟩ := p'
    simp only at h1 h2
    subst h1
    cases e with
    | ok v => exact hk v s s' h2 r hr
    | error l =>
      cases hr
      exact ⟨_, rfl, rfl, h2⟩

theorem monoRun_modifyIf {g : MachineData → Prop} {f : MachineData → MachineData}
    (hg : ∀ a b, StRel M a b → g a → g b) (hf : ∀ a b, StRel M a b → g a → StRel M (f a) (f b)) :
    MonoRun M (modifyIf g f) := by
  intro a b hab r hr
  rw [modifyIf_run] at hr ⊢
  unfold modifyIf at hr ⊢
  by_cases ha : g a
  · rw [UB.assume_bind_of_pos ha] at hr
    rw [UB.assume_bind_of_pos (hg a b hab ha)]
    cases hr
    exact ⟨_, rfl, rfl, hf a b hab ha⟩
  · rw [UB.assume_bind_of_neg ha] at hr
    exact nomatch hr

theorem monoRun_exitIf {α : Type} {g : MachineData → Prop} {f : MachineData → MachineData} (l : Int64)
    (hg : ∀ a b, StRel M a b → g a → g b) (hf : ∀ a b, StRel M a b → g a → StRel M (f a) (f b)) :
    MonoRun M (exitIf g f l : BlockM MachineData α) := by
  intro a b hab r hr
  rw [exitIf_run] at hr ⊢
  unfold exitIf at hr ⊢
  by_cases ha : g a
  · rw [UB.assume_bind_of_pos ha] at hr
    rw [UB.assume_bind_of_pos (hg a b hab ha)]
    cases hr
    exact ⟨_, rfl, rfl, hf a b hab ha⟩
  · rw [UB.assume_bind_of_neg ha] at hr
    exact nomatch hr

theorem monoRun_branch {st c : MachineData → Bool} (l : Int64) (hs : RegFn st) (hc : RegFn c) :
    MonoRun M (branch st c l) := by
  intro a b hab r hr
  rw [branch_run] at hr ⊢
  unfold branch at hr ⊢
  rw [hc.eq hab, hs.eq hab] at hr
  by_cases hcb : c b = true
  · simp only [hcb, ↓reduceIte] at hr ⊢
    by_cases h : st b = true
    · rw [UB.assume_bind_of_pos h] at hr ⊢
      cases hr
      exact ⟨_, rfl, rfl, hab⟩
    · rw [UB.assume_bind_of_neg h] at hr
      exact nomatch hr
  · simp only [hcb, Bool.false_eq_true, ↓reduceIte] at hr ⊢
    cases hr
    exact ⟨_, rfl, rfl, hab⟩

theorem monoRun_peek {β : Type} {c : MachineData → β} (hc : RegFn c) : MonoRun M (peek c) := by
  intro a b hab r hr
  rw [peek_run] at hr ⊢
  unfold peek at hr ⊢
  cases hr
  exact ⟨_, rfl, by rw [hc.eq hab], hab⟩

theorem monoG_true : ∀ a b : MachineData, StRel M a b → (fun _ => True) a → (fun _ => True) b :=
  fun _ _ _ h => h

theorem monoG_loadOk [MemRel M] {n : Nat} {p : MachineData → BitVec 64} (hp : RegFn p) :
    ∀ a b, StRel M a b → loadOk n p a → loadOk n p b := fun a b hab h => by
  unfold loadOk at h ⊢
  rw [← hp.eq hab]
  exact (MemRel.sub hab.mem).loadInt_isSome h

theorem monoG_storeOk [MemRel M] {n : Nat} {p : MachineData → BitVec 64} (hp : RegFn p) :
    ∀ a b, StRel M a b → storeOk n p a → storeOk n p b := monoG_loadOk hp

theorem monoF_setReg64 {g : MachineData → Prop} {r : Reg64} {e : MachineData → BitVec 64} (he : RegFn e) :
    ∀ a b, StRel M a b → g a → StRel M (setReg64 r e a) (setReg64 r e b) := fun a b hab _ =>
  ⟨by simp only [setReg64_regs, hab.regs, he.eq hab], hab.2.1, hab.2.2.1, hab.2.2.2⟩

theorem monoF_loadReg [MemRel M] {n : Nat} {r : Reg64} {p : MachineData → BitVec 64}
    {e : BitVec 64 → MachineData → BitVec 64} (hp : RegFn p) (he : ∀ w, RegFn (e w)) :
    ∀ a b, StRel M a b → loadOk n p a → StRel M (loadReg n r p e a) (loadReg n r p e b) :=
  fun a b hab hl => by
    have hw : word n (p a) a = word n (p b) b := by
      unfold loadOk at hl
      simp only [word, ← hp.eq hab, (MemRel.sub hab.mem).loadInt_get! hl]
    exact ⟨by simp only [loadReg_regs, hab.regs, hw, (he _).eq hab], hab.2.1, hab.2.2.1, hab.2.2.2⟩

theorem monoF_storeWord [MemRel M] {n : Nat} {p v : MachineData → BitVec 64}
    (hp : RegFn p) (hv : RegFn v) :
    ∀ a b, StRel M a b → storeOk n p a → StRel M (storeWord n p v a) (storeWord n p v b) := fun a b hab hs => by
  refine ⟨hab.1, hab.2.1, hab.2.2.1, ?_⟩
  simp only [storeWord_dmem, ← hp.eq hab, hv.eq hab]
  exact MemRel.store hab.mem _ _ _ hs

theorem monoG_retOk [MemRel M] (r₀ : BitVec 64) (ra : Int64) :
    ∀ a b, StRel M a b → retOk r₀ ra a → retOk r₀ ra b := fun a b hab ⟨hr, hra⟩ => by
  refine ⟨hab.regs ▸ hr, ?_⟩
  simp only [MachineData.retAddr_eq] at hra ⊢
  rw [← hab.regs]
  cases hl : Mem.loadInt a.dmem (a.regs.get64 .rsp) 8 with
  | none => rw [hl] at hra; exact nomatch hra
  | some v => rw [hl] at hra; rw [(MemRel.sub hab.mem).loadInt hl]; exact hra

end

/-- Closes `RegFn f` for a function `f` built from register reads. -/
macro "reg_fn" : tactic =>
  `(tactic| (unfold RegFn; intro a b h₁ h₂; simp (config := { failIfUnchanged := false }) only
    [h₁, h₂, sib, stayIn, setReg64_regs]))

/-- Proves `MonoRun M x` for an abstract program of the step vocabulary. -/
macro "mono_run" : tactic =>
  `(tactic| repeat (first
    | with_reducible apply monoRun_modifyIf
    | with_reducible apply monoRun_exitIf
    | with_reducible apply monoRun_peek; reg_fn
    | with_reducible apply monoRun_branch <;> reg_fn
    | with_reducible apply monoRun_pure
    | with_reducible apply monoRun_throw
    | with_reducible apply monoRun_bind <;> intros
    | with_reducible exact monoG_true
    | with_reducible exact monoG_loadOk (by reg_fn)
    | with_reducible exact monoG_storeOk (by reg_fn)
    | with_reducible exact monoG_retOk _ _
    | with_reducible exact monoF_loadReg (by reg_fn) (fun _ => by reg_fn)
    | with_reducible exact monoF_storeWord (by reg_fn) (by reg_fn)
    | with_reducible exact monoF_setReg64 (by reg_fn)))

/-! ## The rules for every memory relation

`derive_rel_rules r₁ … rₙ` adds, for each rule `rᵢ : P ⊑ wrp (ofStateRepr abs) d x Q E` of
`Demo.L1`, the rule `rᵢ_rel : ∀ {M} [MemRel M], P ⊑ wrp (ofStateRel (JRel M)) d x Q E` with the
same precondition. `mono_run` proves that `x` is monotone. -/

open Lean Meta Elab Command Term in
elab "derive_rel_rules " ids:ident+ : command => do
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let newName := name.appendAfter "_rel"
    liftTermElabM do
      let info ← getConstInfo name
      let levels := info.levelParams.map Level.param
      let memTy ← mkArrow (mkConst ``DataMem) (← mkArrow (mkConst ``DataMem) (mkSort 0))
      withLocalDecl `M .implicit memTy fun M => do
      withLocalDecl `inst .instImplicit (mkApp (mkConst ``Ascent.Kraken.MemRel) M) fun inst => do
      forallTelescope info.type fun xs body => do
        let γ ← mkAppM ``Ascent.Concretization.ofStateRel #[mkApp (mkConst ``Ascent.Kraken.JRel) M]
        let body' := body.replace fun e =>
          if e.isAppOfArity ``Ascent.Concretization.ofStateRepr 3 && e.appArg!.isConstOf ``Ascent.Kraken.abs
          then some γ else none
        let w := body.appArg!
        let x := w.getArg! (w.getAppNumArgs - 3)
        let monoTy ← mkAppM ``Ascent.Kraken.MonoRun #[M, x]
        let mono ← Term.elabTermEnsuringType (← `(by mono_run)) monoTy
        Term.synthesizeSyntheticMVarsNoPostponing
        let orig := mkAppN (mkConst name levels) xs
        let pf ← mkAppM ``Ascent.Kraken.wrp_rel_of_abs #[← instantiateMVars mono, orig]
        let pf ← instantiateMVars pf
        let ty ← mkForallFVars (#[M, inst] ++ xs) body'
        let val ← mkLambdaFVars (#[M, inst] ++ xs) pf
        unless ← isDefEq (← inferType val) ty do
          throwError "derive_rel_rules: the derived proof of {name} has the wrong type"
        addDecl <| .thmDecl { name := newName, levelParams := info.levelParams, type := ty, value := val }
    elabCommand (← `(command| attribute [ascend] $(mkIdent newName)))

end Ascent.Kraken




namespace Ascent.Kraken.AInstr

derive_rel_rules wrp_movRegSib8 wrp_addRegSib8 wrp_movSib8Reg wrp_incReg wrp_xorReg32Reg32 wrp_ret
  wrp_movzxRegSib1 wrp_movSib1Reg8 wrp_movRegReg wrp_jmp wrp_jcc wrp_decReg wrp_movRegImm
  wrp_movReg8Imm wrp_addRegReg wrp_shrRegOne wrp_movRegMem wrp_movMemReg wrp_pushReg wrp_popReg
  wrp_subRegImm wrp_addRegImm wrp_movMemReg8 wrp_movMemReg16 wrp_movReg8Mem wrp_movReg16Mem
  wrp_movzxRegMem1 wrp_pushReg16 wrp_popReg16

end Ascent.Kraken.AInstr

namespace Ascent.Kraken.AInstr

section
variable [Host] [FunDecls] {M : DataMem → DataMem → Prop} [MemRel M]
  {Q : Unit → Unit → MachineData → Prop}

@[ascend default + 1] theorem wrp_ret_cons_rel {r₀ : BitVec 64} {ra₀ : Int64} (asz osz : Width) (p : Program)
    (hN : Program.labels (Directive.instr (.regular asz osz .ret) :: p) = []) :
    (fun _ => True)
      ⊑ wrp (ofStateRel (JRel M)) (Directive.instr (.regular asz osz .ret) :: p)
        (exitIf (retOk r₀ ra₀) (setReg64 .rsp fun _ => r₀ + 8) ra₀)
        Q (AddrRel r₀ ra₀) := by
  rw [← exitIf_bind _ _ _ (fun _ => pure ())]
  exact PartialOrder.rel_trans (wrp_ret_rel asz osz) (wrp_cons _ p _ (fun _ => pure ()) hN)

@[ascend default + 1] theorem wrp_jmp_cons_rel {r₀ : BitVec 64} {ra₀ : Int64} (asz osz : Width) (l : Label)
    (p : Program)
    (hN : Program.labels (Directive.instr (.regular asz osz
      (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p) = []) :
    (fun s => (AddrRel r₀ ra₀) (label l) (label l) s)
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p)
          (branch (stayIn (r₀)) (fun _ => true) (label l)) Q (AddrRel r₀ ra₀) := by
  rw [← bind_pure_unit (x := (branch (stayIn (r₀)) (fun _ => true) (label l) : BlockM MachineData Unit))]
  exact PartialOrder.rel_trans (wrp_jmp_rel asz osz l) (wrp_cons _ p _ (fun _ => pure ()) hN)

end

end Ascent.Kraken.AInstr

/-! ## Address computations, 32-bit immediates, and comparisons that a later branch reads

`lea` writes an address without accessing memory. `mov r32, imm` zero-extends. A comparison that
a later `jcc` reads binds its two operands with `peek`; the branch reads the condition of the
flags as the comparison of the bound values (`abs_interp_ofSub`), so instructions that keep the
flags may run between the two. -/

namespace Ascent.Kraken.AInstr

section
variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

theorem Spec.lea_reg_sib (rd b i : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64 (.lea (.low rd .W64) ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg, Reg64s.set_low_W64,
    AddrExpr.zeroExtend_interp_sib, Effects.All]
  exact hn _ hpre

theorem Spec.lea_reg_base_disp (rd b : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (s.regs.get64 b + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64 (.lea (.low rd .W64) ⟨some (.reg b), none, .int64 d⟩)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg, Reg64s.set_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, Effects.All]
  exact hn _ hpre

theorem Spec.mov_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r ((i.toBitVec.setWidth 32).zeroExtend 64) } ⦄
      (Directive.instr (.regular asz .W32 (.mov (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
      Reg64s.set_low_W32, Effects.All]
    exact hn _ hq

end

section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}
  {E : Int64 → Int64 → MachineData → Prop}

@[ascend] theorem wrp_leaSib (rd b i : Reg64) (d : Int64) :
    (fun s => True → Q () () { s with regs := s.regs.set64 rd (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64 (.lea (.low rd .W64) ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))
          (modifyIf (fun _ => True) (setReg64 rd (sib 8 b i d))) Q E := by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Spec.lea_reg_sib (Q := Q) (E := E) rd b i d).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_leaBaseDisp (rd b : Reg64) (d : Int64) :
    (fun s => True → Q () () { s with regs := s.regs.set64 rd (s.regs.get64 b + BitVec.ofInt 64 d.toInt) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64 (.lea (.low rd .W64) ⟨some (.reg b), none, .int64 d⟩)))
          (modifyIf (fun _ => True) (setReg64 rd fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)) Q E := by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Spec.lea_reg_base_disp (Q := Q) (E := E) rd b d).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_movReg32Imm (asz : Width) (r : Reg64) (i : Int64) :
    (fun s => True → Q () () { s with regs := s.regs.set64 r ((i.toBitVec.setWidth 32).zeroExtend 64) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W32 (.mov (.reg (.low r .W32)) (.imm (.int64 i)))))
          (modifyIf (fun _ => True) (setReg64 r fun _ => (i.toBitVec.setWidth 32).zeroExtend 64)) Q E := by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Spec.mov_reg32_imm (Q := Q) (E := E) asz r i).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_cmpRegReg (asz : Width) (ra rb : Reg64)
    {Qp : Unit → BitVec 64 × BitVec 64 → MachineData → Prop} :
    (fun s => ∀ p, PureRefinement (s.regs.get64 ra, s.regs.get64 rb) p True Eq →
      Qp () p { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64 (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
          (peek fun (st : MachineData) => (st.regs.get64 ra, st.regs.get64 rb)) Qp E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_peek, abs_regs] at hs
  obtain ⟨hk, hw⟩ := hs
  refine (Program.WP.Spec.cmp_reg_reg asz ra rb).le_wp s ?_
  show (ofStateRepr abs).post Qp Qa () _
  rw [Concretization.post_pi]
  exact ⟨_, hk _ (PureRefinement.of_rel rfl), hw⟩

@[ascend] theorem wrp_cmpRegImm (asz : Width) (r : Reg64) (i : Int64)
    {Qp : Unit → BitVec 64 × BitVec 64 → MachineData → Prop} :
    (fun s => ∀ p, PureRefinement (s.regs.get64 r, BitVec.setWidth 64 i.toBitVec) p True Eq →
      Qp () p { s with status := StatusFlags.ofSub (s.regs.get64 r) (BitVec.setWidth 64 i.toBitVec) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64 (.cmp (.reg (.low r .W64)) (.imm (.int64 i)))))
          (peek fun (st : MachineData) => (st.regs.get64 r, BitVec.setWidth 64 i.toBitVec)) Qp E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_peek, abs_regs] at hs
  obtain ⟨hk, hw⟩ := hs
  refine (Program.WP.Spec.cmp_reg_imm asz r i).le_wp s ?_
  show (ofStateRepr abs).post Qp Qa () _
  rw [Concretization.post_pi]
  exact ⟨_, hk _ (PureRefinement.of_rel rfl), hw⟩

end

@[ascend_pure] theorem abs_interp_ofSub {cc : CondCode} {a b : BitVec 64} {p : BitVec 64 × BitVec 64}
    {P : Prop} (h : PureRefinement (a, b) p P Eq) :
    PureRefinement (cc.interp (StatusFlags.ofSub a b)) (cc.cmp p.1 p.2) P Eq :=
  fun hp => by rw [CondCode.interp_ofSub, ← h hp]

derive_rel_rules wrp_leaSib wrp_leaBaseDisp wrp_movReg32Imm wrp_cmpRegReg wrp_cmpRegImm

end Ascent.Kraken.AInstr


/-! ## Jumps under the block exit relation

The jump rules for `BlockExit p r₀ E`: a jump that stays in the frame goes to a label of `p`. -/

namespace Ascent.Kraken.AInstr

theorem stayIn_jrel {M : DataMem → DataMem → Prop} {r₀ : BitVec 64} {s a : MachineData} (h : JRel M s a) :
    stayIn r₀ a = stayIn r₀ s := by
  simp only [stayIn, JRel.regs h]

theorem blockExit_jump [Host] {M : DataMem → DataMem → Prop} {p : Program} {r₀ : BitVec 64}
    {E : Int64 → Int64 → MachineData → Prop} {s a : MachineData} {l : Label} (hJ : JRel M s a)
    (hst : stayIn r₀ a = true) (hl : l ∈ Program.labels p) : BlockExit p r₀ E (label l) (label l) s :=
  Or.inl ⟨by rw [← stayIn_jrel hJ]; exact hst, rfl, l, hl, rfl⟩

section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}

@[ascend] theorem wrp_jmp_blk {M : DataMem → DataMem → Prop} {p : Program} {r₀ : BitVec 64} {E : Int64 → Int64 → MachineData → Prop} (asz osz : Width) (l : Label) :
    (fun s => l ∈ Program.labels p)
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction)))))
          (branch (stayIn (r₀)) (fun _ => true) (label l)) Q (BlockExit p r₀ E) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, wp_branch, ↓reduceIte] at hs
  obtain ⟨hmem, a, hJ, hw⟩ := hs
  refine (Program.WP.Spec.jmp_label asz osz l).le_wp s ?_
  show (ofStateRel (JRel M)).post (BlockExit p r₀ E) Ea.1 (label l) s
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
    ofStateRel_pred]
  exact ⟨label l, blockExit_jump hJ hw.1 hmem, a, hJ, hw.2⟩

@[ascend] theorem wrp_jcc_blk {M : DataMem → DataMem → Prop} {p : Program} {r₀ : BitVec 64} {E : Int64 → Int64 → MachineData → Prop} (asz osz : Width) (cc : CondCode) (l : Label) (b : Bool) :
    (fun s => PureRefinement (cc.interp s.status) b True Eq ∧
      (b = true → l ∈ Program.labels p) ∧ (b = false → Q () () s))
      ⊑ wrp (ofStateRel (JRel M)) (Directive.instr (.regular asz osz (.jcc cc l)))
          (branch (stayIn (r₀)) (fun _ => b) (label l)) Q (BlockExit p r₀ E) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, wp_branch] at hs
  obtain ⟨⟨hb, hjmp, hfall⟩, a, hJ, hw⟩ := hs
  have hc : cc.interp s.status = b := hb trivial
  refine (Program.WP.Spec.jcc_label asz osz cc l).le_wp s ⟨fun h => ?_, fun h => ?_⟩
  · rw [hc] at h
    simp only [h, ↓reduceIte] at hw
    show (ofStateRel (JRel M)).post (BlockExit p r₀ E) Ea.1 (label l) s
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
      ofStateRel_pred]
    exact ⟨label l, blockExit_jump hJ hw.1 (hjmp h), a, hJ, hw.2⟩
  · rw [hc] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
    show (ofStateRel (JRel M)).post Q Qa () s
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
      ofStateRel_pred]
    exact ⟨(), hfall h, a, hJ, hw⟩

@[ascend default + 1] theorem wrp_cmpJcc_blk {M : DataMem → DataMem → Prop} {p : Program} {r₀ : BitVec 64} {E : Int64 → Int64 → MachineData → Prop} (asz₁ asz₂ osz : Width) (ra rb : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s =>
      let s' := { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) }
      (cc.cmp (s.regs.get64 ra) (s.regs.get64 rb) = true → l ∈ Program.labels p)
        ∧ (cc.cmp (s.regs.get64 ra) (s.regs.get64 rb) = false → wrp (ofStateRel (JRel M)) p (k ()) Q (BlockExit p r₀ E) s'))
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz₁ .W64
              (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (branch (stayIn (r₀)) (fun st => cc.cmp (st.regs.get64 ra) (st.regs.get64 rb)) (label l) >>= k) Q (BlockExit p r₀ E) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, WPMonadExact.wp_bind_eq,
    wp_branch] at hs
  obtain ⟨⟨hjmp, hfall⟩, a, hJ, hw⟩ := hs
  rw [JRel.regs hJ] at hw
  have h₂ : wp (Directive.instr (.regular asz₂ osz (.jcc cc l)))
      (fun _ => wp p ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea)
      { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) } := by
    refine (Program.WP.Spec.jcc_label asz₂ osz cc l).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, ↓reduceIte] at hw
      show (ofStateRel (JRel M)).post (BlockExit p r₀ E) Ea.1 (label l) _
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, ofStateRel_pred]
      exact ⟨label l, blockExit_jump hJ hw.1 (hjmp h), a, hJ, hw.2⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      refine wrp_transport (P := wrp (ofStateRel (JRel M)) p (k ()) Q (BlockExit p r₀ E)) PartialOrder.rel_refl Qa Ea _ ?_
      simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
      exact ⟨hfall h, a, hJ, hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W64
        (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea) s :=
    (Program.WP.Spec.cmp_reg_reg asz₁ ra rb).le_wp s (Program.wp_cons hN h₂)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN) h₁

@[ascend default + 1] theorem wrp_testJcc_blk {M : DataMem → DataMem → Prop} {p : Program} {r₀ : BitVec 64} {E : Int64 → Int64 → MachineData → Prop} (asz₁ asz₂ osz : Width) (ra rb : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s => ∀ af : Bool,
      let s' := { s with status := StatusFlags.ofLogic (s.regs.get64 ra &&& s.regs.get64 rb) af }
      (cc.cmp (s.regs.get64 ra &&& s.regs.get64 rb) 0 = true → l ∈ Program.labels p)
        ∧ (cc.cmp (s.regs.get64 ra &&& s.regs.get64 rb) 0 = false →
            wrp (ofStateRel (JRel M)) p (k ()) Q (BlockExit p r₀ E) s'))
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz₁ .W64
              (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (branch (stayIn (r₀)) (fun st => cc.cmp (st.regs.get64 ra &&& st.regs.get64 rb) 0) (label l) >>= k) Q (BlockExit p r₀ E) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, WPMonadExact.wp_bind_eq,
    wp_branch] at hs
  obtain ⟨hpre, a, hJ, hw⟩ := hs
  rw [JRel.regs hJ] at hw
  have h₂ : ∀ af : Bool, wp (Directive.instr (.regular asz₂ osz (.jcc cc l)))
      (fun _ => wp p ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea)
      { s with status := StatusFlags.ofLogic (s.regs.get64 ra &&& s.regs.get64 rb) af } := by
    intro af
    obtain ⟨hjmp, hfall⟩ := hpre af
    refine (Program.WP.Spec.jcc_label asz₂ osz cc l).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_ofLogic] at h
      simp only [h, ↓reduceIte] at hw
      show (ofStateRel (JRel M)).post (BlockExit p r₀ E) Ea.1 (label l) _
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, ofStateRel_pred]
      exact ⟨label l, blockExit_jump hJ hw.1 (hjmp h), a, hJ, hw.2⟩
    · rw [CondCode.interp_ofLogic] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      refine wrp_transport (P := wrp (ofStateRel (JRel M)) p (k ()) Q (BlockExit p r₀ E)) PartialOrder.rel_refl Qa Ea _ ?_
      simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
      exact ⟨hfall h, a, hJ, hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W64
        (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea) s :=
    (Program.WP.Spec.test_reg_reg asz₁ ra rb).le_wp s fun af => Program.wp_cons hN (h₂ af)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN) h₁

@[ascend default + 1] theorem wrp_subJcc_blk {M : DataMem → DataMem → Prop} {p : Program} {r₀ : BitVec 64} {E : Int64 → Int64 → MachineData → Prop} (asz₁ asz₂ osz : Width) (rd rs : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s =>
      let s' := { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status := StatusFlags.ofSub (s.regs.get64 rd) (s.regs.get64 rs) }
      (cc.cmp (s.regs.get64 rd) (s.regs.get64 rs) = true → l ∈ Program.labels p)
        ∧ (cc.cmp (s.regs.get64 rd) (s.regs.get64 rs) = false → wrp (ofStateRel (JRel M)) p (k ()) Q (BlockExit p r₀ E) s'))
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz₁ .W64
              (.sub (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (peek (fun st => cc.cmp (st.regs.get64 rd) (st.regs.get64 rs)) >>= fun c =>
            modifyIf (fun _ => True) (setReg64 rd fun st => st.regs.get64 rd - st.regs.get64 rs) >>= fun _ =>
            branch (stayIn (r₀)) (fun _ => c) (label l) >>= k) Q (BlockExit p r₀ E) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, WPMonadExact.wp_bind_eq, wp_peek,
    wp_modifyIf, wp_branch] at hs
  obtain ⟨⟨hjmp, hfall⟩, a, hJ, -, hw⟩ := hs
  rw [JRel.regs hJ] at hw
  have hJ' : JRel M { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status := StatusFlags.ofSub (s.regs.get64 rd) (s.regs.get64 rs) }
      (setReg64 rd (fun st => st.regs.get64 rd - st.regs.get64 rs) a) :=
    ⟨by simp only [setReg64_regs, abs_regs, JRel.regs hJ], hJ.2.1, hJ.2.2.1, hJ.2.2.2⟩
  have h₂ : wp (Directive.instr (.regular asz₂ osz (.jcc cc l)))
      (fun _ => wp p ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea)
      { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status := StatusFlags.ofSub (s.regs.get64 rd) (s.regs.get64 rs) } := by
    refine (Program.WP.Spec.jcc_label asz₂ osz cc l).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, ↓reduceIte] at hw
      show (ofStateRel (JRel M)).post (BlockExit p r₀ E) Ea.1 (label l) _
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, ofStateRel_pred]
      exact ⟨label l, blockExit_jump hJ' hw.1 (hjmp h), _, hJ', hw.2⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      refine wrp_transport (P := wrp (ofStateRel (JRel M)) p (k ()) Q (BlockExit p r₀ E)) PartialOrder.rel_refl Qa Ea _ ?_
      simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
      exact ⟨hfall h, _, hJ', hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W64
        (.sub (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea) s :=
    (Spec.sub_reg_reg asz₁ rd rs).le_wp s (Program.wp_cons hN h₂)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN) h₁

@[ascend default + 2] theorem wrp_cmpJccJcc_blk {M : DataMem → DataMem → Prop} {p : Program} {r₀ : BitVec 64} {E : Int64 → Int64 → MachineData → Prop} (asz₁ asz₂ asz₃ osz₂ osz₃ : Width) (ra rb : Reg64)
    (c₁ c₂ : CondCode) (l₁ l₂ : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN₂ : Program.labels (Directive.instr (.regular asz₂ osz₂ (.jcc c₁ l₁))
      :: Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p) = [])
    (hN₃ : Program.labels (Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p) = []) :
    (fun s =>
      let s' := { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) }
      (c₁.cmp (s.regs.get64 ra) (s.regs.get64 rb) = true → l₁ ∈ Program.labels p)
        ∧ (c₁.cmp (s.regs.get64 ra) (s.regs.get64 rb) = false →
          (c₂.cmp (s.regs.get64 ra) (s.regs.get64 rb) = true → l₂ ∈ Program.labels p)
            ∧ (c₂.cmp (s.regs.get64 ra) (s.regs.get64 rb) = false →
              wrp (ofStateRel (JRel M)) p (k ()) Q (BlockExit p r₀ E) s')))
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz₁ .W64
              (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))
            :: Directive.instr (.regular asz₂ osz₂ (.jcc c₁ l₁))
            :: Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p)
          (branch (stayIn (r₀)) (fun st => c₁.cmp (st.regs.get64 ra) (st.regs.get64 rb)) (label l₁) >>= fun _ =>
            branch (stayIn (r₀)) (fun st => c₂.cmp (st.regs.get64 ra) (st.regs.get64 rb)) (label l₂) >>= k) Q (BlockExit p r₀ E) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, WPMonadExact.wp_bind_eq,
    wp_branch] at hs
  obtain ⟨⟨hjmp₁, hfall₁⟩, a, hJ, hw⟩ := hs
  rw [JRel.regs hJ] at hw
  let s' := { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) }
  have hpost : ∀ (l : Label) (cl : Int64), (BlockExit p r₀ E) (label l) cl s' → Ea.1 cl a →
      (ofStateRel (JRel M)).post (BlockExit p r₀ E) Ea.1 (label l) s' := by
    intro l cl he hea
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
      meet_prop_eq_and, ofStateRel_pred]
    exact ⟨cl, he, a, hJ, hea⟩
  have h₃ : wp (Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)))
      (fun _ => wp p ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea) s' →
      wp (Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p) ((ofStateRel (JRel M)).post Q Qa)
        (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea) s' := Program.wp_cons hN₃
  have h₂ : wp (Directive.instr (.regular asz₂ osz₂ (.jcc c₁ l₁)))
      (fun _ => wp (Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea) s' := by
    refine (Program.WP.Spec.jcc_label asz₂ osz₂ c₁ l₁).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, ↓reduceIte] at hw
      exact hpost l₁ _ (blockExit_jump hJ hw.1 (hjmp₁ h)) hw.2
    · rw [CondCode.interp_ofSub] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      obtain ⟨hjmp₂, hfall₂⟩ := hfall₁ h
      refine h₃ ((Program.WP.Spec.jcc_label asz₃ osz₃ c₂ l₂).le_wp _ ⟨fun h' => ?_, fun h' => ?_⟩)
      · rw [CondCode.interp_ofSub] at h'
        simp only [h', ↓reduceIte] at hw
        exact hpost l₂ _ (blockExit_jump hJ hw.1 (hjmp₂ h')) hw.2
      · rw [CondCode.interp_ofSub] at h'
        simp only [h', Bool.false_eq_true, ↓reduceIte] at hw
        refine wrp_transport (P := wrp (ofStateRel (JRel M)) p (k ()) Q (BlockExit p r₀ E)) PartialOrder.rel_refl Qa Ea _ ?_
        simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
        exact ⟨hfall₂ h', a, hJ, hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W64
        (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz₂ (.jcc c₁ l₁))
          :: Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea) s :=
    (Program.WP.Spec.cmp_reg_reg asz₁ ra rb).le_wp s (Program.wp_cons hN₂ h₂)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN₂) h₁

@[ascend default + 1] theorem wrp_testJcc8_blk {M : DataMem → DataMem → Prop} {p : Program} {r₀ : BitVec 64} {E : Int64 → Int64 → MachineData → Prop} (asz₁ asz₂ osz : Width) (ra rb : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s => ∀ af : Bool,
      let v := (s.regs.get64 ra).take 8 &&& (s.regs.get64 rb).take 8
      let s' := { s with status := StatusFlags.from_result v { cf := false, af := af, of := false } }
      (cc.interp (StatusFlags.from_result v { cf := false, af := false, of := false }) = true →
          l ∈ Program.labels p)
        ∧ (cc.interp (StatusFlags.from_result v { cf := false, af := false, of := false }) = false →
          wrp (ofStateRel (JRel M)) p (k ()) Q (BlockExit p r₀ E) s'))
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz₁ .W8
              (.test (.reg (.low ra .W8)) (.regOrMem (.reg (.low rb .W8)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (branch (stayIn (r₀)) (fun st => cc.interp (StatusFlags.from_result
              ((st.regs.get64 ra).take 8 &&& (st.regs.get64 rb).take 8)
              { cf := false, af := false, of := false })) (label l) >>= k) Q (BlockExit p r₀ E) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, WPMonadExact.wp_bind_eq,
    wp_branch] at hs
  obtain ⟨hpre, a, hJ, hw⟩ := hs
  rw [JRel.regs hJ] at hw
  have h₂ : ∀ af : Bool, wp (Directive.instr (.regular asz₂ osz (.jcc cc l)))
      (fun _ => wp p ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea)
      { s with status := StatusFlags.from_result ((s.regs.get64 ra).take 8 &&& (s.regs.get64 rb).take 8) { cf := false, af := af, of := false } } := by
    intro af
    obtain ⟨hjmp, hfall⟩ := hpre af
    refine (Program.WP.Spec.jcc_label asz₂ osz cc l).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_from_result_af] at h
      simp only [h, ↓reduceIte] at hw
      show (ofStateRel (JRel M)).post (BlockExit p r₀ E) Ea.1 (label l) _
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, ofStateRel_pred]
      exact ⟨label l, blockExit_jump hJ hw.1 (hjmp h), a, hJ, hw.2⟩
    · rw [CondCode.interp_from_result_af] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      refine wrp_transport (P := wrp (ofStateRel (JRel M)) p (k ()) Q (BlockExit p r₀ E)) PartialOrder.rel_refl Qa Ea _ ?_
      simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
      exact ⟨hfall h, a, hJ, hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W8
        (.test (.reg (.low ra .W8)) (.regOrMem (.reg (.low rb .W8))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (BlockExit p r₀ E) Ea) s :=
    (Spec.test_reg8_reg8 asz₁ ra rb).le_wp s fun af => Program.wp_cons hN (h₂ af)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN) h₁

end

end Ascent.Kraken.AInstr
