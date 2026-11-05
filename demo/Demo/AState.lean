import Demo.Cfg
import Kraken.X64.WP.Spec

/-!
# The abstract machine

`AState` is the machine state of the L1 layer: the registers st a function, the status flags with
`af` cleared, and kraken's data memory. `abs` reads it off a `MachineData`, and the concretization of
the layer is `ofStateRepr abs`.

An abstract instruction is a guarded update of `AState`: `modifyIf g f` updates by `f` when the guard
`g` holds and is undefined behaviour otherwise, `exitIf g f l` updates and throws the label `l`, and
`branch c l` throws `l` when `c` holds. The operations in `AInstr` name one such step per machine
instruction, and each `@[ascend]` rule pairs it with kraken's spec of that instruction.
-/

open Std.WP Lean.Order Ascent
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)
open scoped Program.WP

def StatusFlags.noAF (st : StatusFlags) : StatusFlags := { st with af := false }

theorem CondCode.interp_noAF (cc : CondCode) (st : StatusFlags) :
    cc.interp st.noAF = cc.interp st := by
  cases cc <;> rfl

namespace Ascent.Kraken

structure AState where
  regs : Reg64 → BitVec 64
  status : StatusFlags
  mem : DataMem

def abs (s : MachineData) : AState := ⟨s.regs.get64, s.status.noAF, s.dmem⟩

def AState.setReg (st : AState) (r : Reg64) (v : BitVec 64) : AState :=
  { st with regs := fun r' => if r' = r then v else st.regs r' }

def AState.sib8 (st : AState) (b i : Reg64) (d : Int64) : BitVec 64 :=
  st.regs b + st.regs i * 8 + BitVec.ofInt 64 d.toInt

/-- A store of eight bytes at `a` leaves the return slot of the frame intact. -/
def AState.frameSafe (st : AState) (a : BitVec 64) : Bool :=
  decide (8 ≤ (st.regs .rsp - a).toNat) && decide (8 ≤ (a - st.regs .rsp).toNat)

@[simp, vcgen_simp] theorem abs_regs (s : MachineData) : (abs s).regs = s.regs.get64 := rfl

/-! The register fields of the abstraction, one rule per register as for `Reg64s.get64`, so that a
finisher sees `s.regs.r.toBitVec` and never `get64`. -/
@[simp, vcgen_simp, grind =] theorem abs_regs_rax (s : MachineData) : (abs s).regs .rax = s.regs.rax.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_rbx (s : MachineData) : (abs s).regs .rbx = s.regs.rbx.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_rcx (s : MachineData) : (abs s).regs .rcx = s.regs.rcx.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_rdx (s : MachineData) : (abs s).regs .rdx = s.regs.rdx.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_rsi (s : MachineData) : (abs s).regs .rsi = s.regs.rsi.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_rdi (s : MachineData) : (abs s).regs .rdi = s.regs.rdi.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_rsp (s : MachineData) : (abs s).regs .rsp = s.regs.rsp.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_rbp (s : MachineData) : (abs s).regs .rbp = s.regs.rbp.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_r8 (s : MachineData) : (abs s).regs .r8 = s.regs.r8.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_r9 (s : MachineData) : (abs s).regs .r9 = s.regs.r9.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_r10 (s : MachineData) : (abs s).regs .r10 = s.regs.r10.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_r11 (s : MachineData) : (abs s).regs .r11 = s.regs.r11.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_r12 (s : MachineData) : (abs s).regs .r12 = s.regs.r12.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_r13 (s : MachineData) : (abs s).regs .r13 = s.regs.r13.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_r14 (s : MachineData) : (abs s).regs .r14 = s.regs.r14.toBitVec := rfl
@[simp, vcgen_simp, grind =] theorem abs_regs_r15 (s : MachineData) : (abs s).regs .r15 = s.regs.r15.toBitVec := rfl
@[simp, vcgen_simp] theorem abs_status (s : MachineData) : (abs s).status = s.status.noAF := rfl
@[simp, vcgen_simp] theorem abs_mem (s : MachineData) : (abs s).mem = s.dmem := rfl

theorem abs_regs_set64 (s : MachineData) (r : Reg64) (v : BitVec 64) :
    (s.regs.set64 r v).get64 = fun r' => if r' = r then v else s.regs.get64 r' := by
  funext r'
  exact Reg64s.get64_set64 s.regs r r' v

namespace AInstr

/-! ## The three step shapes -/

def modifyIf (g : AState → Bool) (f : AState → AState) : BlockM AState Unit :=
  fun st => if g st then pure (.ok (), f st) else UB.fail

def exitIf (g : AState → Bool) (f : AState → AState) (l : CfgLabel) : BlockM AState Unit :=
  fun st => if g st then pure (.error l, f st) else UB.fail

def branch (c : AState → Bool) (l : CfgLabel) : BlockM AState Unit :=
  fun st => if c st then pure (.error l, st) else pure (.ok (), st)

section
variable (Qa : Unit → AState → Prop) (Ea : (CfgLabel → AState → Prop) × EStack⟨⟩) (st : AState)

theorem modifyIf_run (g f) : (modifyIf g f).run.run st = modifyIf g f st := rfl
theorem exitIf_run (g f l) : (exitIf g f l).run.run st = exitIf g f l st := rfl
theorem branch_run (c l) : (branch c l).run.run st = branch c l st := rfl

theorem wp_modifyIf (g f) :
    wp (modifyIf g f) Qa Ea st = (g st = true ∧ Qa () (f st)) := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, modifyIf_run]
  unfold modifyIf
  split
  · simp only [UB.wp_pure_eq, *, true_and]
    rfl
  · simp only [UB.wp_fail_eq, bot_prop_eq, *, Bool.false_eq_true, false_and]

theorem wp_exitIf (g f l) :
    wp (exitIf g f l) Qa Ea st = (g st = true ∧ Ea.1 l (f st)) := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, exitIf_run]
  unfold exitIf
  split
  · simp only [UB.wp_pure_eq, *, true_and]
    rfl
  · simp only [UB.wp_fail_eq, bot_prop_eq, *, Bool.false_eq_true, false_and]

theorem wp_branch (c l) :
    wp (branch c l) Qa Ea st = if c st then Ea.1 l st else Qa () st := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, branch_run]
  unfold branch
  split
  · simp only [UB.wp_pure_eq, *, ↓reduceIte]
    rfl
  · simp only [UB.wp_pure_eq, *, Bool.false_eq_true, ↓reduceIte]
    rfl

end

/-! ## The generic rules -/

section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}
  {E : Int64 → CfgLabel → MachineData → Prop}

theorem wrp_modifyIf {d : Directive} {pre : MachineData → Prop} {upd : MachineData → MachineData}
    (hspec : ∀ (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop) s,
      pre s → Q () (upd s) → wp d Q E s)
    {g : AState → Bool} {f : AState → AState}
    (hsim : ∀ s, g (abs s) = true → pre s ∧ abs (upd s) = f (abs s)) :
    (fun s => g (abs s) = true → Q () () (upd s)) ⊑ wrp (ofStateRepr abs) d (modifyIf g f) Q E := by
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
    {g : AState → Bool} {f : AState → AState}
    (hpre : ∀ s, g (abs s) = true → pre s)
    (habs : ∀ s x, g (abs s) = true → abs (upd x s) = f (abs s)) :
    (fun s => g (abs s) = true → ∀ x, Q () () (upd x s))
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
    {g : AState → Bool} {f : AState → AState}
    (hsim : ∀ s, g (abs s) = true → pre s ∧ abs (upd s) = f (abs s)) (l : CfgLabel) :
    (fun s => g (abs s) = true → E (ex s) l (upd s))
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

/-! ## The instructions of the example -/

/-- The eight bytes at the scaled-index address are mapped. -/
def sib8Loaded (b i : Reg64) (d : Int64) (st : AState) : Bool :=
  (Mem.loadInt st.mem (st.sib8 b i d) 8).isSome

/-- The store at the scaled-index address is mapped and leaves the frame intact. -/
def sib8Storable (b i : Reg64) (d : Int64) (st : AState) : Bool :=
  sib8Loaded b i d st && st.frameSafe (st.sib8 b i d)

/-- The return slot is mapped. -/
def retLoaded (st : AState) : Bool := (Mem.loadInt st.mem (st.regs .rsp) 8).isSome

@[simp, vcgen_simp] theorem sib8Loaded_eq (b i : Reg64) (d : Int64) (st : AState) :
    sib8Loaded b i d st = (Mem.loadInt st.mem (st.sib8 b i d) 8).isSome := rfl
@[simp, vcgen_simp] theorem sib8Storable_eq (b i : Reg64) (d : Int64) (st : AState) :
    sib8Storable b i d st = (sib8Loaded b i d st && st.frameSafe (st.sib8 b i d)) := rfl
@[simp, vcgen_simp] theorem retLoaded_eq (st : AState) :
    retLoaded st = (Mem.loadInt st.mem (st.regs .rsp) 8).isSome := rfl

/-! The grind theory of the guards: the scaled-index address without displacement, and the frame
guard as its two bounds, which kraken's `Blocks.Disjoint.of_sub` turns into disjointness. -/

@[simp, vcgen_simp, grind =] theorem AState.sib8_zero (st : AState) (b i : Reg64) :
    st.sib8 b i 0 = st.regs b + st.regs i * 8 := by
  simp [AState.sib8]

theorem AState.frameSafe_eq (st : AState) (a : BitVec 64) :
    (st.frameSafe a = true) = (8 ≤ (st.regs .rsp - a).toNat ∧ 8 ≤ (a - st.regs .rsp).toNat) := by
  simp [AState.frameSafe]

/-- A store at a frame-safe address leaves the return slot as it was. The guard itself is the
pattern, so a finisher instantiates the lemma in one step. -/
theorem Mem.loadInt_storeInt_of_frameSafe {st : AState} {a x : BitVec 64} (h : st.frameSafe a = true)
    (hrsp : st.regs .rsp = x) {m : DataMem} {v : Int} :
    (Mem.storeInt m a 8 v).loadInt x 8 = m.loadInt x 8 := by
  rw [AState.frameSafe_eq, hrsp] at h
  exact Mem.loadInt_storeInt_of_disjoint (Mem.Blocks.Disjoint.of_sub h.1 h.2) _

grind_pattern Mem.loadInt_storeInt_of_frameSafe =>
  Mem.loadInt (Mem.storeInt m a 8 v) x 8, AState.frameSafe st a

attribute [grind =] abs_regs abs_mem sib8Storable_eq sib8Loaded_eq

def movRegSib8 (r b i : Reg64) (d : Int64) : BlockM AState Unit :=
  modifyIf (sib8Loaded b i d) fun st =>
    st.setReg r (BitVec.ofInt 64 (Mem.loadInt st.mem (st.sib8 b i d) 8).get!)

def addRegSib8 (rd b i : Reg64) (d : Int64) : BlockM AState Unit :=
  modifyIf (sib8Loaded b i d) fun st =>
    let x := BitVec.ofInt 64 (Mem.loadInt st.mem (st.sib8 b i d) 8).get!
    let y := st.regs rd
    { st.setReg rd (x + y) with status := (StatusFlags.ofAdd x y).noAF }

def movSib8Reg (b i : Reg64) (d : Int64) (rs : Reg64) : BlockM AState Unit :=
  modifyIf (sib8Storable b i d) fun st =>
    { st with mem := Mem.storeInt st.mem (st.sib8 b i d) 8 (st.regs rs).toInt }

def incReg (r : Reg64) : BlockM AState Unit :=
  modifyIf (fun _ => true) fun st =>
    { st.setReg r (st.regs r + 1) with status := (StatusFlags.ofInc (st.regs r) st.status.cf).noAF }

def cmpRegReg (ra rb : Reg64) : BlockM AState Unit :=
  modifyIf (fun _ => true) fun st =>
    { st with status := (StatusFlags.ofSub (st.regs ra) (st.regs rb)).noAF }

def testRegReg (ra rb : Reg64) : BlockM AState Unit :=
  modifyIf (fun _ => true) fun st =>
    { st with status := (StatusFlags.ofLogic (st.regs ra &&& st.regs rb) false).noAF }

def xorReg32Reg32 (rd rs : Reg64) : BlockM AState Unit :=
  modifyIf (fun _ => true) fun st =>
    let v := (st.regs rd).take 32 ^^^ (st.regs rs).take 32
    { st.setReg rd (v.zeroExtend 64) with status := (StatusFlags.ofLogic v false).noAF }

def jcc (cc : CondCode) (l : Label) : BlockM AState Unit :=
  branch (fun st => cc.interp st.status) (.label l)

def ret : BlockM AState Unit :=
  exitIf retLoaded (fun st => st.setReg .rsp (st.regs .rsp + 8)) .exit

/-! ## The rules of the example -/

section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}
  {E : Int64 → CfgLabel → MachineData → Prop}

@[ascend] theorem wrp_movRegSib8 (r b i : Reg64) (d : Int64) :
    (fun s => sib8Loaded b i d (abs s) = true →
      Q () () { s with regs := s.regs.set64 r (BitVec.ofInt 64
        (Mem.loadInt s.dmem (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) 8).get!) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64
            (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
          (movRegSib8 r b i d) Q E :=
  by
  refine wrp_modifyIf (g := sib8Loaded b i d)
    (fun Q E s hp hq => (Program.WP.Spec.mov_reg_sib8 (Q := Q) (E := E) r b i d).le_wp s ⟨hp, hq⟩) ?_
  intro s hg
  exact ⟨hg, by simp [abs, AState.setReg, AState.sib8, abs_regs_set64]⟩

@[ascend] theorem wrp_addRegSib8 (rd b i : Reg64) (d : Int64) :
    (fun s => sib8Loaded b i d (abs s) = true →
      let x := BitVec.ofInt 64
        (Mem.loadInt s.dmem (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) 8).get!
      let y := s.regs.get64 rd
      Q () () { s with
        regs := s.regs.set64 rd (x + y), status := StatusFlags.ofAdd x y })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64
            (.add (.reg (.low rd .W64)) (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
          (addRegSib8 rd b i d) Q E :=
  by
  refine wrp_modifyIf (g := sib8Loaded b i d)
    (fun Q E s hp hq => (Program.WP.Spec.add_reg_sib8 (Q := Q) (E := E) rd b i d).le_wp s ⟨hp, hq⟩) ?_
  intro s hg
  exact ⟨hg, by simp [abs, AState.setReg, AState.sib8, abs_regs_set64, StatusFlags.noAF]⟩

@[ascend] theorem wrp_movSib8Reg (b i : Reg64) (d : Int64) (rs : Reg64) :
    (fun s => sib8Storable b i d (abs s) = true →
      Q () () { s with
        dmem := Mem.storeInt s.dmem (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt)
          8 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64
            (.mov (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W64))))))
          (movSib8Reg b i d rs) Q E :=
  by
  refine wrp_modifyIf (g := sib8Storable b i d)
    (fun Q E s hp hq => (Program.WP.Spec.mov_sib8_reg (Q := Q) (E := E) b i d rs).le_wp s ⟨hp, hq⟩) ?_
  intro s hg
  exact ⟨((Bool.and_eq_true _ _).mp hg).1, by simp [abs, AState.sib8]⟩

@[ascend] theorem wrp_incReg (asz : Width) (r : Reg64) :
    (fun s => true = true → Q () () { s with
        regs := s.regs.set64 r (s.regs.get64 r + 1),
        status := StatusFlags.ofInc (s.regs.get64 r) s.status.cf })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz .W64 (.inc (.reg (.low r .W64)))))
          (incReg r) Q E :=
  by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => true)
    (fun Q E s _ hq => (Program.WP.Spec.inc_reg (Q := Q) (E := E) asz r).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, by simp [abs, AState.setReg, abs_regs_set64, StatusFlags.noAF]⟩

@[ascend] theorem wrp_cmpRegReg (asz : Width) (ra rb : Reg64) :
    (fun s => true = true →
      Q () () { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64
            (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
          (cmpRegReg ra rb) Q E :=
  by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => true)
    (fun Q E s _ hq => (Program.WP.Spec.cmp_reg_reg (Q := Q) (E := E) asz ra rb).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, by simp [abs, StatusFlags.noAF]⟩

@[ascend] theorem wrp_testRegReg (asz : Width) (ra rb : Reg64) :
    (fun s => true = true → ∀ af : Bool, Q () () { s with
        status := StatusFlags.ofLogic (s.regs.get64 ra &&& s.regs.get64 rb) af })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64
            (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
          (testRegReg ra rb) Q E :=
  by
  refine wrp_modifyIf_forall (pre := fun _ => True) (g := fun _ => true)
    (fun Q E s _ hq => (Program.WP.Spec.test_reg_reg (Q := Q) (E := E) asz ra rb).le_wp s hq)
    (fun _ _ => trivial) ?_
  intro s af _
  simp [abs, StatusFlags.noAF, StatusFlags.ofLogic]

@[ascend] theorem wrp_xorReg32Reg32 (asz : Width) (rd rs : Reg64) :
    (fun s => true = true →
      let v := (s.regs.get64 rd).take 32 ^^^ (s.regs.get64 rs).take 32
      ∀ af : Bool, Q () () { s with
        regs := s.regs.set64 rd (v.zeroExtend 64),
        status := StatusFlags.ofLogic v af })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W32
            (.xor (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
          (xorReg32Reg32 rd rs) Q E :=
  by
  refine wrp_modifyIf_forall (pre := fun _ => True) (g := fun _ => true)
    (fun Q E s _ hq => (Program.WP.Spec.xor_reg32_reg32 (Q := Q) (E := E) asz rd rs).le_wp s hq)
    (fun _ _ => trivial) ?_
  intro s af _
  simp [abs, AState.setReg, abs_regs_set64, StatusFlags.noAF, StatusFlags.ofLogic]

@[ascend] theorem wrp_jcc (asz osz : Width) (cc : CondCode) (l : Label) :
    (fun s => (cc.interp s.status = true → E (label l) (.label l) s)
        ∧ (cc.interp s.status = false → Q () () s))
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz (.jcc cc l))) (jcc cc l) Q E :=
  wrp_branch asz osz cc l

@[ascend] theorem wrp_ret (asz osz : Width) :
    (fun s => retLoaded (abs s) = true →
      E s.retAddr.get! .exit { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz .ret)) ret Q E :=
  by
  refine wrp_exitIf (pre := fun s => s.retAddr.isSome = true) (g := retLoaded)
    (fun Q E s hp he => (Program.WP.Spec.ret (Q := Q) (E := E) asz osz).le_wp s ⟨hp, he⟩) ?_ .exit
  intro s hg
  exact ⟨by simpa [abs, MachineData.retAddr_eq] using hg, by simp [abs, AState.setReg, abs_regs_set64]⟩

theorem exitIf_bind (g : AState → Bool) (f : AState → AState) (l : CfgLabel)
    (k : Unit → BlockM AState Unit) : (exitIf g f l >>= k) = exitIf g f l := by
  apply ExceptT.ext
  apply StateT.ext
  intro st
  rw [ExceptT.run_bind, StateT.run_bind, exitIf_run]
  unfold exitIf
  by_cases h : g st = true
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- A `ret` ends the block, and the directives after it are unreachable. -/
@[ascend default + 1] theorem wrp_ret_cons (asz osz : Width) (p : Program)
    (hN : Program.labels (Directive.instr (.regular asz osz .ret) :: p) = []) :
    (fun s => retLoaded (abs s) = true →
      E s.retAddr.get! .exit { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz .ret) :: p) ret Q E := by
  show _ ⊑ wrp (ofStateRepr abs) _ (exitIf retLoaded _ .exit) Q E
  rw [← exitIf_bind retLoaded _ .exit (fun _ => pure ())]
  exact PartialOrder.rel_trans (wrp_ret asz osz) (wrp_cons _ p ret (fun _ => pure ()) hN)

end

end AInstr

end Ascent.Kraken
