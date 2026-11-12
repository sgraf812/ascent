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

theorem monoF_storeWord [MemRel M] {g : MachineData → Prop} {n : Nat} {p v : MachineData → BitVec 64}
    (hp : RegFn p) (hv : RegFn v) :
    ∀ a b, StRel M a b → g a → StRel M (storeWord n p v a) (storeWord n p v b) := fun a b hab _ => by
  refine ⟨hab.1, hab.2.1, hab.2.2.1, ?_⟩
  simp only [storeWord_dmem, hp.eq hab, hv.eq hab]
  exact MemRel.store hab.mem _ _ _

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
