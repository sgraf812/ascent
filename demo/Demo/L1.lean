import Demo.Cfg
import Kraken.X64.WP.Spec

/-!
# The first layer

The abstract state of the first layer is kraken's `MachineData` with the `af` flag cleared, since
the specs of `test` and `xor` leave `af` open. `abs` is that projection, and the concretization of
the layer is `ofStateRepr abs`.

An abstract instruction is a guarded update of the state: `modifyIf g f` updates by `f` when the
guard `g` holds and is undefined behaviour otherwise, `exitIf g f l` updates and throws the label
`l`, and `branch c l` throws `l` when the machine condition `c` holds. The operations in `AInstr`
name one such step per machine instruction, and each `@[ascend]` rule pairs it with kraken's spec of
that instruction. The update of a step is the post state of the spec, and a guard is the
precondition of the spec stated on the abstract state.
-/

open Std.WP Lean.Order Ascent
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)
open scoped Program.WP

def StatusFlags.noAF (st : StatusFlags) : StatusFlags := { st with af := false }

theorem CondCode.interp_noAF (cc : CondCode) (st : StatusFlags) :
    cc.interp st.noAF = cc.interp st := by
  cases cc <;> rfl

namespace Ascent.Kraken

def abs (s : MachineData) : MachineData := { s with status := s.status.noAF }

@[simp, vcgen_simp, grind =] theorem abs_regs (s : MachineData) : (abs s).regs = s.regs := rfl
@[simp, vcgen_simp, grind =] theorem abs_zmms (s : MachineData) : (abs s).zmms = s.zmms := rfl
@[simp, vcgen_simp] theorem abs_status (s : MachineData) : (abs s).status = s.status.noAF := rfl
@[simp, vcgen_simp, grind =] theorem abs_dmem (s : MachineData) : (abs s).dmem = s.dmem := rfl

namespace AInstr

/-! ## The three step shapes -/

noncomputable def modifyIf (g : MachineData → Prop) (f : MachineData → MachineData) :
    BlockM MachineData Unit :=
  fun st => UB.guardRet (g st) (.ok (), f st)

noncomputable def exitIf (g : MachineData → Prop) (f : MachineData → MachineData) (l : CfgLabel) :
    BlockM MachineData Unit :=
  fun st => UB.guardRet (g st) (.error l, f st)

def branch (c : MachineData → Bool) (l : CfgLabel) : BlockM MachineData Unit :=
  fun st => if c st then pure (.error l, st) else pure (.ok (), st)

section
variable (Qa : Unit → MachineData → Prop) (Ea : (CfgLabel → MachineData → Prop) × EStack⟨⟩) (st : MachineData)

theorem modifyIf_run (g f) : (modifyIf g f).run.run st = modifyIf g f st := rfl
theorem exitIf_run (g f l) : (exitIf g f l).run.run st = exitIf g f l st := rfl
theorem branch_run (c l) : (branch c l).run.run st = branch c l st := rfl

theorem wp_modifyIf (g f) :
    wp (modifyIf g f) Qa Ea st = (g st ∧ Qa () (f st)) := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, modifyIf_run]
  unfold modifyIf
  by_cases h : g st
  · rw [UB.guardRet_of_pos h]
    simp only [UB.wp_pure_eq, h, true_and]
    rfl
  · rw [UB.guardRet_of_neg h]
    simp only [UB.wp_fail_eq, bot_prop_eq, h, false_and]

theorem wp_exitIf (g f l) :
    wp (exitIf g f l) Qa Ea st = (g st ∧ Ea.1 l (f st)) := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, exitIf_run]
  unfold exitIf
  by_cases h : g st
  · rw [UB.guardRet_of_pos h]
    simp only [UB.wp_pure_eq, h, true_and]
    rfl
  · rw [UB.guardRet_of_neg h]
    simp only [UB.wp_fail_eq, bot_prop_eq, h, false_and]

theorem wp_branch (c l) :
    wp (branch c l) Qa Ea st = if c st then Ea.1 l st else Qa () st := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, branch_run]
  unfold branch
  split
  · simp only [UB.wp_pure_eq, *]
    rfl
  · simp only [UB.wp_pure_eq, *]
    rfl

end

/-! ## The generic rules -/

section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}
  {E : Int64 → CfgLabel → MachineData → Prop}

theorem wrp_modifyIf {d : Directive} {pre : MachineData → Prop} {upd : MachineData → MachineData}
    (hspec : ∀ (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop) s,
      pre s → Q () (upd s) → wp d Q E s)
    {g : MachineData → Prop} {f : MachineData → MachineData}
    (hsim : ∀ s, g (abs s) → pre s ∧ abs (upd s) = f (abs s)) :
    (fun s => g (abs s) → Q () () (upd s)) ⊑ wrp (ofStateRepr abs) d (modifyIf g f) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_modifyIf] at hs
  obtain ⟨hQ, hg, hQa⟩ := hs
  obtain ⟨hpre, habs⟩ := hsim s hg
  refine hspec _ _ s hpre ?_
  show (ofStateRepr abs).post Q Qa () (upd s)
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
    ofStateRepr_pred]
  exact ⟨(), hQ hg, habs ▸ hQa⟩

theorem wrp_modifyIf_forall {ι : Type} {d : Directive} {pre : MachineData → Prop}
    {upd : ι → MachineData → MachineData}
    (hspec : ∀ (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop) s,
      pre s → (∀ x, Q () (upd x s)) → wp d Q E s)
    {g : MachineData → Prop} {f : MachineData → MachineData}
    (hpre : ∀ s, g (abs s) → pre s)
    (habs : ∀ s x, g (abs s) → abs (upd x s) = f (abs s)) :
    (fun s => g (abs s) → ∀ x, Q () () (upd x s))
      ⊑ wrp (ofStateRepr abs) d (modifyIf g f) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_modifyIf] at hs
  obtain ⟨hQ, hg, hQa⟩ := hs
  refine hspec _ _ s (hpre s hg) fun x => ?_
  show (ofStateRepr abs).post Q Qa () (upd x s)
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
    ofStateRepr_pred]
  exact ⟨(), hQ hg x, habs s x hg ▸ hQa⟩

theorem wrp_exitIf {d : Directive} {pre : MachineData → Prop} {ex : MachineData → Int64}
    {upd : MachineData → MachineData}
    (hspec : ∀ (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop) s,
      pre s → E (ex s) (upd s) → wp d Q E s)
    {g : MachineData → Prop} {f : MachineData → MachineData}
    (hsim : ∀ s, g (abs s) → pre s ∧ abs (upd s) = f (abs s)) (l : CfgLabel) :
    (fun s => g (abs s) → E (ex s) l (upd s))
      ⊑ wrp (ofStateRepr abs) d (exitIf g f l) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_exitIf] at hs
  obtain ⟨hE, hg, hEa⟩ := hs
  obtain ⟨hpre, habs⟩ := hsim s hg
  refine hspec _ _ s hpre ?_
  show (ofStateRepr abs).post E Ea.1 (ex s) (upd s)
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
    ofStateRepr_pred]
  exact ⟨l, hE hg, habs ▸ hEa⟩

theorem wrp_branch (asz osz : Width) (cc : CondCode) (l : Label) :
    (fun s => (cc.interp s.status = true → E (label l) (.label l) s)
        ∧ (cc.interp s.status = false → Q () () s))
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz (.jcc cc l)))
          (branch (fun st => cc.interp st.status) (.label l)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_branch] at hs
  obtain ⟨⟨hjmp, hfall⟩, hw⟩ := hs
  have hc : cc.interp (abs s).status = cc.interp s.status := CondCode.interp_noAF cc s.status
  rw [hc] at hw
  refine (Program.WP.Spec.jcc_label asz osz cc l).le_wp s ⟨fun h => ?_, fun h => ?_⟩
  · show (ofStateRepr abs).post E Ea.1 (label l) s
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
      meet_prop_eq_and, ofStateRepr_pred]
    rw [h] at hw
    exact ⟨.label l, hjmp h, by simpa using hw⟩
  · show (ofStateRepr abs).post Q Qa () s
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
      meet_prop_eq_and, ofStateRepr_pred]
    rw [h] at hw
    exact ⟨(), hfall h, by simpa using hw⟩

end

/-! ## The instructions of the example

A memory operand `d(b, i, 8)` reads the address `a st`. The guard of a load is that the eight bytes
are mapped. The guard of a store adds that the cell is apart from the return slot of the frame. -/

noncomputable def movRegSib8 (r b i : Reg64) (d : Int64) : BlockM MachineData Unit :=
  let a (st : MachineData) := st.regs.get64 b + st.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
  modifyIf (fun st => (Mem.loadInt st.dmem (a st) 8).isSome = true) fun st =>
    { st with regs := st.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt st.dmem (a st) 8).get!) }

noncomputable def addRegSib8 (rd b i : Reg64) (d : Int64) : BlockM MachineData Unit :=
  let a (st : MachineData) := st.regs.get64 b + st.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
  modifyIf (fun st => (Mem.loadInt st.dmem (a st) 8).isSome = true) fun st =>
    let x := BitVec.ofInt 64 (Mem.loadInt st.dmem (a st) 8).get!
    let y := st.regs.get64 rd
    { st with regs := st.regs.set64 rd (x + y), status := (StatusFlags.ofAdd x y).noAF }

noncomputable def movSib8Reg (b i : Reg64) (d : Int64) (rs : Reg64) : BlockM MachineData Unit :=
  let a (st : MachineData) := st.regs.get64 b + st.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
  modifyIf (fun st => (Mem.loadInt st.dmem (a st) 8).isSome = true
      ∧ Mem.Blocks.Disjoint [(st.regs.get64 .rsp, 8)] [(a st, 8)]) fun st =>
    { st with dmem := Mem.storeInt st.dmem (a st) 8 (st.regs.get64 rs).toInt }

noncomputable def incReg (r : Reg64) : BlockM MachineData Unit :=
  modifyIf (fun _ => True) fun st =>
    { st with regs := st.regs.set64 r (st.regs.get64 r + 1),
              status := (StatusFlags.ofInc (st.regs.get64 r) st.status.cf).noAF }

noncomputable def cmpRegReg (ra rb : Reg64) : BlockM MachineData Unit :=
  modifyIf (fun _ => True) fun st =>
    { st with status := (StatusFlags.ofSub (st.regs.get64 ra) (st.regs.get64 rb)).noAF }

noncomputable def testRegReg (ra rb : Reg64) : BlockM MachineData Unit :=
  modifyIf (fun _ => True) fun st =>
    { st with status := (StatusFlags.ofLogic (st.regs.get64 ra &&& st.regs.get64 rb) false).noAF }

noncomputable def xorReg32Reg32 (rd rs : Reg64) : BlockM MachineData Unit :=
  modifyIf (fun _ => True) fun st =>
    let v := (st.regs.get64 rd).take 32 ^^^ (st.regs.get64 rs).take 32
    { st with regs := st.regs.set64 rd (v.zeroExtend 64), status := (StatusFlags.ofLogic v false).noAF }

def jcc (cc : CondCode) (l : Label) : BlockM MachineData Unit :=
  branch (fun st => cc.interp st.status) (.label l)

noncomputable def ret : BlockM MachineData Unit :=
  exitIf (fun st => (Mem.loadInt st.dmem (st.regs.get64 .rsp) 8).isSome = true)
    (fun st => { st with regs := st.regs.set64 .rsp (st.regs.get64 .rsp + 8) }) .exit

/-! ## The rules of the example -/

section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}
  {E : Int64 → CfgLabel → MachineData → Prop}

@[ascend] theorem wrp_movRegSib8 (r b i : Reg64) (d : Int64) :
    (fun s =>
      let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 8).isSome = true →
        Q () () { s with regs := s.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64
            (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
          (movRegSib8 r b i d) Q E :=
  by
  refine wrp_modifyIf (g := fun st => (Mem.loadInt st.dmem (st.regs.get64 b + st.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) 8).isSome = true)
    (fun Q E s hp hq => (Program.WP.Spec.mov_reg_sib8 (Q := Q) (E := E) r b i d).le_wp s ⟨hp, hq⟩) ?_
  intro s hg
  exact ⟨hg, rfl⟩

@[ascend] theorem wrp_addRegSib8 (rd b i : Reg64) (d : Int64) :
    (fun s =>
      let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 8).isSome = true →
      let x := BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!
      let y := s.regs.get64 rd
      Q () () { s with
        regs := s.regs.set64 rd (x + y), status := StatusFlags.ofAdd x y })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64
            (.add (.reg (.low rd .W64)) (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
          (addRegSib8 rd b i d) Q E :=
  by
  refine wrp_modifyIf (g := fun st => (Mem.loadInt st.dmem (st.regs.get64 b + st.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) 8).isSome = true)
    (fun Q E s hp hq => (Program.WP.Spec.add_reg_sib8 (Q := Q) (E := E) rd b i d).le_wp s ⟨hp, hq⟩) ?_
  intro s hg
  exact ⟨hg, rfl⟩

@[ascend] theorem wrp_movSib8Reg (b i : Reg64) (d : Int64) (rs : Reg64) :
    (fun s =>
      let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 8).isSome = true → Mem.Blocks.Disjoint [(s.regs.get64 .rsp, 8)] [(a, 8)] →
        Q () () { s with dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64
            (.mov (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W64))))))
          (movSib8Reg b i d rs) Q E :=
  by
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf
    (g := fun st => (Mem.loadInt st.dmem (st.regs.get64 b + st.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) 8).isSome = true
      ∧ Mem.Blocks.Disjoint [(st.regs.get64 .rsp, 8)] [(st.regs.get64 b + st.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt, 8)])
    (fun Q E s hp hq => (Program.WP.Spec.mov_sib8_reg (Q := Q) (E := E) b i d rs).le_wp s ⟨hp, hq⟩)
    fun s hg => ⟨hg.1, rfl⟩)
  intro s h hg
  exact h hg.1 hg.2

@[ascend] theorem wrp_incReg (asz : Width) (r : Reg64) :
    (fun s => True → Q () () { s with
        regs := s.regs.set64 r (s.regs.get64 r + 1),
        status := StatusFlags.ofInc (s.regs.get64 r) s.status.cf })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz .W64 (.inc (.reg (.low r .W64)))))
          (incReg r) Q E :=
  by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.inc_reg (Q := Q) (E := E) asz r).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_cmpRegReg (asz : Width) (ra rb : Reg64) :
    (fun s => True →
      Q () () { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64
            (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
          (cmpRegReg ra rb) Q E :=
  by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.cmp_reg_reg (Q := Q) (E := E) asz ra rb).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_testRegReg (asz : Width) (ra rb : Reg64) :
    (fun s => True → ∀ af : Bool, Q () () { s with
        status := StatusFlags.ofLogic (s.regs.get64 ra &&& s.regs.get64 rb) af })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64
            (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
          (testRegReg ra rb) Q E :=
  by
  refine wrp_modifyIf_forall (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.test_reg_reg (Q := Q) (E := E) asz ra rb).le_wp s hq)
    (fun _ _ => trivial) ?_
  intro s af _
  simp [abs, StatusFlags.noAF, StatusFlags.ofLogic]

@[ascend] theorem wrp_xorReg32Reg32 (asz : Width) (rd rs : Reg64) :
    (fun s => True →
      let v := (s.regs.get64 rd).take 32 ^^^ (s.regs.get64 rs).take 32
      ∀ af : Bool, Q () () { s with
        regs := s.regs.set64 rd (v.zeroExtend 64),
        status := StatusFlags.ofLogic v af })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W32
            (.xor (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
          (xorReg32Reg32 rd rs) Q E :=
  by
  refine wrp_modifyIf_forall (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.xor_reg32_reg32 (Q := Q) (E := E) asz rd rs).le_wp s hq)
    (fun _ _ => trivial) ?_
  intro s af _
  simp [abs, StatusFlags.noAF, StatusFlags.ofLogic]

@[ascend] theorem wrp_jcc (asz osz : Width) (cc : CondCode) (l : Label) :
    (fun s => (cc.interp s.status = true → E (label l) (.label l) s)
        ∧ (cc.interp s.status = false → Q () () s))
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz (.jcc cc l))) (jcc cc l) Q E :=
  wrp_branch asz osz cc l

@[ascend] theorem wrp_ret (asz osz : Width) :
    (fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).isSome = true →
      E s.retAddr.get! .exit { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz .ret)) ret Q E :=
  by
  refine wrp_exitIf (pre := fun s => s.retAddr.isSome = true)
    (g := fun st => (Mem.loadInt st.dmem (st.regs.get64 .rsp) 8).isSome = true)
    (fun Q E s hp he => (Program.WP.Spec.ret (Q := Q) (E := E) asz osz).le_wp s ⟨hp, he⟩) ?_ .exit
  intro s hg
  exact ⟨by simpa [MachineData.retAddr_eq] using hg, rfl⟩

theorem exitIf_bind (g : MachineData → Prop) (f : MachineData → MachineData) (l : CfgLabel)
    (k : Unit → BlockM MachineData Unit) : (exitIf g f l >>= k) = exitIf g f l := by
  apply ExceptT.ext
  apply StateT.ext
  intro st
  rw [ExceptT.run_bind, StateT.run_bind, exitIf_run]
  unfold exitIf
  by_cases h : g st
  · rw [UB.guardRet_of_pos h]
    rfl
  · rw [UB.guardRet_of_neg h]
    rfl

/-- A `ret` ends the block, and the directives after it are unreachable. -/
@[ascend default + 1] theorem wrp_ret_cons (asz osz : Width) (p : Program)
    (hN : Program.labels (Directive.instr (.regular asz osz .ret) :: p) = []) :
    (fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).isSome = true →
      E s.retAddr.get! .exit { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz .ret) :: p) ret Q E := by
  show _ ⊑ wrp (ofStateRepr abs) _ (exitIf _ _ .exit) Q E
  rw [← exitIf_bind _ _ .exit (fun _ => pure ())]
  exact PartialOrder.rel_trans (wrp_ret asz osz) (wrp_cons _ p ret (fun _ => pure ()) hN)

end

end AInstr

end Ascent.Kraken
