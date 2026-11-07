import Demo.Cfg
import Kraken.X64.WP.Spec

/-!
# The first layer

The abstract state of the first layer is kraken's `MachineData` with the status flags cleared.
`abs` is that projection, and the concretization of the layer is `ofStateRepr abs`. A flag is
written by an arithmetic instruction and read by the conditional jump that follows, so the pair
`cmp ra, rb; jcc cc, l` is one abstract instruction, a branch on the comparison `cc.cmp` of the
two registers, and no abstract instruction reads or writes a flag.

An abstract instruction is a guarded update of the state: `modifyIf g f` updates by `f` when the
guard `g` holds and is undefined behaviour otherwise, `exitIf g f l` updates and throws the label
`l`, and `branch c l` throws `l` when the condition `c` holds. The operations in `AInstr` name one
such step per machine instruction, and each `@[ascend]` rule pairs it with kraken's spec of that
instruction. The update of a step is the post state of the spec, and a guard is the precondition
of the spec stated on the abstract state.
-/

open Std.WP Lean.Order Ascent
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)
open scoped Program.WP

def StatusFlags.clear : StatusFlags := ⟨false, false, false, false, false, false⟩

/-! ## The comparison a condition code decides

After `cmp a, b` the flags are `StatusFlags.ofSub a b`, and a condition code reads them as a
comparison of `a` and `b`: `z` is `a == b`, `l` is `a.slt b`, `a` is `b.ult a`, and so on. The codes
`o`, `no`, `s`, `ns`, `p`, `np` compare nothing and stay flag reads. After `test a, b` the flags are
`StatusFlags.ofLogic (a &&& b) af`, which every condition code reads as the comparison of `a &&& b`
with `0`. -/

def CondCode.cmp (cc : CondCode) (a b : BitVec 64) : Bool :=
  match cc with
  | .z => a == b
  | .nz => a != b
  | .c => a.ult b
  | .nc => b.ule a
  | .be => a.ule b
  | .a => b.ult a
  | .l => a.slt b
  | .ge => b.sle a
  | .le => a.sle b
  | .g => b.slt a
  | cc => cc.interp (StatusFlags.ofSub a b)

theorem StatusFlags.zf_ofSub_eq (a b : BitVec 64) : (StatusFlags.ofSub a b).zf = (a == b) := by
  rw [StatusFlags.zf_ofSub, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.zero_eq]
  constructor
  · intro h
    have := congrArg (· + b) h
    simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using this
  · rintro rfl
    exact BitVec.sub_self a

theorem StatusFlags.cf_ofSub_eq (a b : BitVec 64) : (StatusFlags.ofSub a b).cf = a.ult b := by
  rw [StatusFlags.cf_ofSub, BitVec.unsigned_eq, BitVec.unsigned_eq, BitVec.unsigned_eq,
    BitVec.ult_eq_decide, Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
  have ⟨h₁, h₂⟩ := BitVec.toNat_sub_cases a b
  have ha := a.isLt
  have hb := b.isLt
  by_cases h : b.toNat ≤ a.toNat
  · rw [h₁ h]; omega
  · rw [h₂ (by omega)]; omega

theorem StatusFlags.neg_ofSub_eq (a b : BitVec 64) : (StatusFlags.ofSub a b).neg = a.slt b := by
  rw [StatusFlags.neg_ofSub, BitVec.slt_eq_decide]
  exact decide_eq_decide.mpr (BitVec.toInt_lt_toInt_iff_flip a b).symm

theorem CondCode.interp_ofSub (cc : CondCode) (a b : BitVec 64) :
    cc.interp (StatusFlags.ofSub a b) = cc.cmp a b := by
  have hz := StatusFlags.zf_ofSub_eq a b
  have hc := StatusFlags.cf_ofSub_eq a b
  have hn := StatusFlags.neg_ofSub_eq a b
  cases cc <;> simp only [CondCode.cmp, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c,
    CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, CondCode.interp_l_neg,
    CondCode.interp_ge_neg, CondCode.interp_le_neg, CondCode.interp_g_neg, hz, hc, hn]
  all_goals
    rw [Bool.eq_iff_iff]
    first
    | (simp only [BitVec.ult_eq_decide, BitVec.ule_eq_decide, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', decide_eq_true_iff, decide_eq_false_iff_not, beq_iff_eq,
        beq_eq_false_iff_ne, bne_iff_ne, ne_eq, BitVec.toNat_eq]) <;> omega
    | (simp only [BitVec.slt_eq_decide, BitVec.sle_eq_decide, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', decide_eq_true_iff, decide_eq_false_iff_not, beq_iff_eq,
        beq_eq_false_iff_ne, ne_eq, ← BitVec.toInt_inj]) <;> omega

theorem StatusFlags.ofLogic_eq (v : BitVec 64) (af : Bool) :
    StatusFlags.ofLogic v af = { StatusFlags.ofSub v 0 with af := af } := by
  simp [StatusFlags.ofLogic, StatusFlags.ofSub, StatusFlags.from_result]

theorem CondCode.interp_af (cc : CondCode) (s : StatusFlags) (af : Bool) :
    cc.interp { s with af := af } = cc.interp s := by
  cases cc <;> rfl

theorem CondCode.interp_ofLogic (cc : CondCode) (v : BitVec 64) (af : Bool) :
    cc.interp (StatusFlags.ofLogic v af) = cc.cmp v 0 := by
  rw [StatusFlags.ofLogic_eq, CondCode.interp_af, CondCode.interp_ofSub]

namespace Ascent.Kraken

def abs (s : MachineData) : MachineData := { s with status := .clear }

@[simp, vcgen_simp, grind =] theorem abs_regs (s : MachineData) : (abs s).regs = s.regs := rfl
@[simp, vcgen_simp, grind =] theorem abs_zmms (s : MachineData) : (abs s).zmms = s.zmms := rfl
@[simp, vcgen_simp] theorem abs_status (s : MachineData) : (abs s).status = .clear := rfl
@[simp, vcgen_simp, grind =] theorem abs_dmem (s : MachineData) : (abs s).dmem = s.dmem := rfl

namespace AInstr

/-! ## The three step shapes -/

section
variable {σ : Type}

noncomputable def modifyIf (g : σ → Prop) (f : σ → σ) : BlockM σ Unit :=
  fun st => UB.guardRet (g st) (.ok (), f st)

noncomputable def exitIf (g : σ → Prop) (f : σ → σ) (l : CfgLabel) : BlockM σ Unit :=
  fun st => UB.guardRet (g st) (.error l, f st)

def branch (c : σ → Bool) (l : CfgLabel) : BlockM σ Unit :=
  fun st => if c st then pure (.error l, st) else pure (.ok (), st)

end

section
variable {σ : Type} (Qa : Unit → σ → Prop) (Ea : (CfgLabel → σ → Prop) × EStack⟨⟩) (st : σ)

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

end

/-! ## The instructions of the example

A memory operand `d(b, i, 8)` reads the address `sib8 b i d st`. The guard `loadOk8 a` of a load
from the address `a st` is that the eight bytes are mapped. The guard `storeOk8 a` of a store adds
that the cell is apart from the return slot of the frame. Each instruction is a state function, and
its step is `modifyIf` of its guard and that function. -/

def sib8 (b i : Reg64) (d : Int64) (st : MachineData) : BitVec 64 :=
  st.regs.get64 b + st.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt

def loadOk8 (a : MachineData → BitVec 64) (st : MachineData) : Prop :=
  (Mem.loadInt st.dmem (a st) 8).isSome = true

def storeOk8 (a : MachineData → BitVec 64) (st : MachineData) : Prop :=
  loadOk8 a st ∧ Mem.Blocks.Disjoint [(st.regs.get64 .rsp, 8)] [(a st, 8)]

def retOk (st : MachineData) : Prop := (Mem.loadInt st.dmem (st.regs.get64 .rsp) 8).isSome = true

def movRegSib8 (r b i : Reg64) (d : Int64) (st : MachineData) : MachineData :=
  { st with regs := st.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt st.dmem (sib8 b i d st) 8).get!) }

def addRegSib8 (rd b i : Reg64) (d : Int64) (st : MachineData) : MachineData :=
  { st with regs := st.regs.set64 rd (BitVec.ofInt 64 (Mem.loadInt st.dmem (sib8 b i d st) 8).get! + st.regs.get64 rd) }

def movSib8Reg (b i : Reg64) (d : Int64) (rs : Reg64) (st : MachineData) : MachineData :=
  { st with dmem := Mem.storeInt st.dmem (sib8 b i d st) 8 (st.regs.get64 rs).toInt }

def incReg (r : Reg64) (st : MachineData) : MachineData :=
  { st with regs := st.regs.set64 r (st.regs.get64 r + 1) }

def xorReg32Reg32 (rd rs : Reg64) (st : MachineData) : MachineData :=
  { st with regs := st.regs.set64 rd (((st.regs.get64 rd).take 32 ^^^ (st.regs.get64 rs).take 32).zeroExtend 64) }

def ret (st : MachineData) : MachineData :=
  { st with regs := st.regs.set64 .rsp (st.regs.get64 .rsp + 8) }

/-! ## Normal forms of the steps

Every state function of the example is one of three writes. `setReg64 r e` writes the value `e st`
to the register `r`. `loadReg8 r a e` reads the word `w` at the address `a st` and writes `e w st`
to `r`. `storeWord8 a v` writes the word `v st` to the address `a st`. The equations below put each
instruction into its normal form, and the guards `loadOk8` and `storeOk8` are stated over the
address of the step. -/

def word8 (a : BitVec 64) (st : MachineData) : BitVec 64 :=
  BitVec.ofInt 64 (Mem.loadInt st.dmem a 8).get!

def setReg64 (r : Reg64) (e : MachineData → BitVec 64) (st : MachineData) : MachineData :=
  { st with regs := st.regs.set64 r (e st) }

def loadReg8 (r : Reg64) (a : MachineData → BitVec 64) (e : BitVec 64 → MachineData → BitVec 64)
    (st : MachineData) : MachineData :=
  { st with regs := st.regs.set64 r (e (word8 (a st) st) st) }

def storeWord8 (a v : MachineData → BitVec 64) (st : MachineData) : MachineData :=
  { st with dmem := Mem.storeInt st.dmem (a st) 8 (v st).toInt }

section
variable (st : MachineData)

@[vcgen_simp] theorem setReg64_regs (r : Reg64) (e : MachineData → BitVec 64) :
    (setReg64 r e st).regs = st.regs.set64 r (e st) := rfl
@[vcgen_simp] theorem setReg64_dmem (r : Reg64) (e : MachineData → BitVec 64) :
    (setReg64 r e st).dmem = st.dmem := rfl
@[vcgen_simp] theorem loadReg8_regs (r : Reg64) (a : MachineData → BitVec 64)
    (e : BitVec 64 → MachineData → BitVec 64) :
    (loadReg8 r a e st).regs = st.regs.set64 r (e (word8 (a st) st) st) := rfl
@[vcgen_simp] theorem loadReg8_dmem (r : Reg64) (a : MachineData → BitVec 64)
    (e : BitVec 64 → MachineData → BitVec 64) : (loadReg8 r a e st).dmem = st.dmem := rfl
@[vcgen_simp] theorem storeWord8_regs (a v : MachineData → BitVec 64) :
    (storeWord8 a v st).regs = st.regs := rfl
@[vcgen_simp] theorem storeWord8_dmem (a v : MachineData → BitVec 64) :
    (storeWord8 a v st).dmem = Mem.storeInt st.dmem (a st) 8 (v st).toInt := rfl

end

@[vcgen_simp] theorem movRegSib8_eq (r b i : Reg64) (d : Int64) :
    movRegSib8 r b i d = loadReg8 r (sib8 b i d) (fun w _ => w) := rfl
@[vcgen_simp] theorem addRegSib8_eq (rd b i : Reg64) (d : Int64) :
    addRegSib8 rd b i d = loadReg8 rd (sib8 b i d) (fun w st => w + st.regs.get64 rd) := rfl
@[vcgen_simp] theorem movSib8Reg_eq (b i : Reg64) (d : Int64) (rs : Reg64) :
    movSib8Reg b i d rs = storeWord8 (sib8 b i d) (fun st => st.regs.get64 rs) := rfl
@[vcgen_simp] theorem incReg_eq (r : Reg64) :
    incReg r = setReg64 r (fun st => st.regs.get64 r + 1) := rfl
@[vcgen_simp] theorem xorReg32Reg32_eq (rd rs : Reg64) :
    xorReg32Reg32 rd rs = setReg64 rd
      (fun st => ((st.regs.get64 rd).take 32 ^^^ (st.regs.get64 rs).take 32).zeroExtend 64) := rfl
@[vcgen_simp] theorem ret_eq : ret = setReg64 .rsp (fun st => st.regs.get64 .rsp + 8) := rfl
@[vcgen_simp] theorem retOk_eq : retOk = loadOk8 (fun st => st.regs.get64 .rsp) := rfl

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
          (modifyIf (loadOk8 (sib8 b i d)) (movRegSib8 r b i d)) Q E :=
  by
  refine wrp_modifyIf (g := loadOk8 (sib8 b i d))
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
          (modifyIf (loadOk8 (sib8 b i d)) (addRegSib8 rd b i d)) Q E :=
  by
  refine wrp_modifyIf (g := loadOk8 (sib8 b i d))
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
          (modifyIf (storeOk8 (sib8 b i d)) (movSib8Reg b i d rs)) Q E :=
  by
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf
    (g := storeOk8 (sib8 b i d))
    (fun Q E s hp hq => (Program.WP.Spec.mov_sib8_reg (Q := Q) (E := E) b i d rs).le_wp s ⟨hp, hq⟩)
    fun s hg => ⟨hg.1, rfl⟩)
  intro s h hg
  exact h hg.1 hg.2

@[ascend] theorem wrp_incReg (asz : Width) (r : Reg64) :
    (fun s => True → Q () () { s with
        regs := s.regs.set64 r (s.regs.get64 r + 1),
        status := StatusFlags.ofInc (s.regs.get64 r) s.status.cf })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz .W64 (.inc (.reg (.low r .W64)))))
          (modifyIf (fun _ => True) (incReg r)) Q E :=
  by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.inc_reg (Q := Q) (E := E) asz r).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_xorReg32Reg32 (asz : Width) (rd rs : Reg64) :
    (fun s => True →
      let v := (s.regs.get64 rd).take 32 ^^^ (s.regs.get64 rs).take 32
      ∀ af : Bool, Q () () { s with
        regs := s.regs.set64 rd (v.zeroExtend 64),
        status := StatusFlags.ofLogic v af })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W32
            (.xor (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
          (modifyIf (fun _ => True) (xorReg32Reg32 rd rs)) Q E :=
  by
  refine wrp_modifyIf_forall (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.xor_reg32_reg32 (Q := Q) (E := E) asz rd rs).le_wp s hq)
    (fun _ _ => trivial) ?_
  intro s af _
  rfl

/-- `cmp ra, rb; jcc cc, l` branches on the comparison of the two registers. The flags the pair
writes are cleared by `abs`. -/
@[ascend default + 1] theorem wrp_cmpJcc (asz₁ asz₂ osz : Width) (ra rb : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s =>
      let s' := { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) }
      (cc.cmp (s.regs.get64 ra) (s.regs.get64 rb) = true → E (label l) (.label l) s')
        ∧ (cc.cmp (s.regs.get64 ra) (s.regs.get64 rb) = false → wrp (ofStateRepr abs) p (k ()) Q E s'))
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz₁ .W64
              (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (branch (fun st => cc.cmp (st.regs.get64 ra) (st.regs.get64 rb)) (.label l) >>= k) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq,
    wp_branch, abs_regs] at hs
  obtain ⟨⟨hjmp, hfall⟩, hw⟩ := hs
  have h₂ : wp (Directive.instr (.regular asz₂ osz (.jcc cc l)))
      (fun _ => wp p ((ofStateRepr abs).post Q Qa) (EPostsConcretization.ePosts (ofStateRepr abs) E Ea))
      (EPostsConcretization.ePosts (ofStateRepr abs) E Ea)
      { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) } := by
    refine (Program.WP.Spec.jcc_label asz₂ osz cc l).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, ↓reduceIte] at hw
      show (ofStateRepr abs).post E Ea.1 (label l) _
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, ofStateRepr_pred]
      exact ⟨.label l, hjmp h, hw⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      refine wrp_transport (P := wrp (ofStateRepr abs) p (k ()) Q E) PartialOrder.rel_refl Qa Ea _ ?_
      simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]
      exact ⟨hfall h, hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W64
        (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
        ((ofStateRepr abs).post Q Qa) (EPostsConcretization.ePosts (ofStateRepr abs) E Ea))
      (EPostsConcretization.ePosts (ofStateRepr abs) E Ea) s :=
    (Program.WP.Spec.cmp_reg_reg asz₁ ra rb).le_wp s (Program.wp_cons hN h₂)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN) h₁

/-- `test ra, rb; jcc cc, l` branches on the comparison of `ra &&& rb` with zero. -/
@[ascend default + 1] theorem wrp_testJcc (asz₁ asz₂ osz : Width) (ra rb : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s => ∀ af : Bool,
      let s' := { s with status := StatusFlags.ofLogic (s.regs.get64 ra &&& s.regs.get64 rb) af }
      (cc.cmp (s.regs.get64 ra &&& s.regs.get64 rb) 0 = true → E (label l) (.label l) s')
        ∧ (cc.cmp (s.regs.get64 ra &&& s.regs.get64 rb) 0 = false →
            wrp (ofStateRepr abs) p (k ()) Q E s'))
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz₁ .W64
              (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (branch (fun st => cc.cmp (st.regs.get64 ra &&& st.regs.get64 rb) 0) (.label l) >>= k) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq,
    wp_branch, abs_regs] at hs
  obtain ⟨hpre, hw⟩ := hs
  have h₂ : ∀ af : Bool, wp (Directive.instr (.regular asz₂ osz (.jcc cc l)))
      (fun _ => wp p ((ofStateRepr abs).post Q Qa) (EPostsConcretization.ePosts (ofStateRepr abs) E Ea))
      (EPostsConcretization.ePosts (ofStateRepr abs) E Ea)
      { s with status := StatusFlags.ofLogic (s.regs.get64 ra &&& s.regs.get64 rb) af } := by
    intro af
    obtain ⟨hjmp, hfall⟩ := hpre af
    refine (Program.WP.Spec.jcc_label asz₂ osz cc l).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_ofLogic] at h
      simp only [h, ↓reduceIte] at hw
      show (ofStateRepr abs).post E Ea.1 (label l) _
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, ofStateRepr_pred]
      exact ⟨.label l, hjmp h, hw⟩
    · rw [CondCode.interp_ofLogic] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      refine wrp_transport (P := wrp (ofStateRepr abs) p (k ()) Q E) PartialOrder.rel_refl Qa Ea _ ?_
      simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]
      exact ⟨hfall h, hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W64
        (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
        ((ofStateRepr abs).post Q Qa) (EPostsConcretization.ePosts (ofStateRepr abs) E Ea))
      (EPostsConcretization.ePosts (ofStateRepr abs) E Ea) s :=
    (Program.WP.Spec.test_reg_reg asz₁ ra rb).le_wp s fun af => Program.wp_cons hN (h₂ af)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN) h₁

@[ascend] theorem wrp_ret (asz osz : Width) :
    (fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).isSome = true →
      E s.retAddr.get! .exit { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz .ret)) (exitIf retOk ret .exit) Q E :=
  by
  refine wrp_exitIf (pre := fun s => s.retAddr.isSome = true)
    (g := retOk)
    (fun Q E s hp he => (Program.WP.Spec.ret (Q := Q) (E := E) asz osz).le_wp s ⟨hp, he⟩) ?_ .exit
  intro s hg
  exact ⟨by simpa [MachineData.retAddr_eq, retOk] using hg, rfl⟩

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
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz .ret) :: p) (exitIf retOk ret .exit) Q E := by
  rw [← exitIf_bind _ _ .exit (fun _ => pure ())]
  exact PartialOrder.rel_trans (wrp_ret asz osz) (wrp_cons _ p _ (fun _ => pure ()) hN)

end

end AInstr

end Ascent.Kraken
