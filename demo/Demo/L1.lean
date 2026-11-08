import Demo.Cfg
import Ascent.PureRefinement
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

theorem CondCode.cmp_nz_eq_true (a b : BitVec 64) : (CondCode.nz.cmp a b = true) = (a ≠ b) := by
  simp [CondCode.cmp]

theorem CondCode.cmp_le_eq_true (a b : BitVec 64) : (CondCode.le.cmp a b = true) = (a.toInt ≤ b.toInt) := by
  simp [CondCode.cmp, BitVec.sle_iff_toInt_le]

theorem StatusFlags.zf_ofSub_eq (a b : BitVec 64) : (StatusFlags.ofSub a b).zf = (a == b) := by
  rw [StatusFlags.zf_ofSub, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.zero_eq]
  constructor
  · intro h
    have := congrArg (· + b) h
    simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using this
  · rintro rfl
    exact BitVec.sub_self a

theorem StatusFlags.cf_ofSub_eq (a b : BitVec 64) : (StatusFlags.ofSub a b).cf = a.ult b := by
  rw [StatusFlags.cf_ofSub, Bool.eq_iff_iff, BitVec.usubOverflow_eq_true_iff, BitVec.ult_eq_decide,
    decide_eq_true_iff]

theorem CondCode.interp_ofSub (cc : CondCode) (a b : BitVec 64) :
    cc.interp (StatusFlags.ofSub a b) = cc.cmp a b := by
  have hz := StatusFlags.zf_ofSub_eq a b
  have hc := StatusFlags.cf_ofSub_eq a b
  have hn := StatusFlags.neg_ofSub a b
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
  fun st => UB.assume (g st) >>= fun _ => pure (.ok (), f st)

noncomputable def exitIf {α : Type} (g : σ → Prop) (f : σ → σ) (l : CfgLabel) : BlockM σ α :=
  fun st => UB.assume (g st) >>= fun _ => pure (.error l, f st)

def branch (c : σ → Bool) (l : CfgLabel) : BlockM σ Unit :=
  fun st => if c st then pure (.error l, st) else pure (.ok (), st)

def peek {β : Type} (c : σ → β) : BlockM σ β :=
  fun st => pure (.ok (c st), st)

end

section
variable {σ : Type} (Qa : Unit → σ → Prop) (Ea : (CfgLabel → σ → Prop) × EStack⟨⟩) (st : σ)

theorem modifyIf_run (g f) : (modifyIf g f).run.run st = modifyIf g f st := rfl
theorem exitIf_run {α : Type} (g f l) : (exitIf g f l : BlockM σ α).run.run st = exitIf g f l st := rfl
theorem branch_run (c l) : (branch c l).run.run st = branch c l st := rfl
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

theorem exitIf_bind {σ α β : Type} (g : σ → Prop) (f : σ → σ) (l : CfgLabel)
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

/-! ## Addresses, guards and the writes of a step

A memory operand `d(b, i, k)` reads the address `sib k b i d st`. The guard `loadOk n a` of a load
of `n` bytes from the address `a st` is that the bytes are mapped. The guard `storeOk n a` of a store
adds that the cell is apart from the return slot of the frame.

The step of an instruction is `modifyIf` of its guard and one of three writes. `setReg64 r e`
writes the value `e st` to the register `r`. `loadReg n r a e` reads the `n`-byte word `w` at the
address `a st`, zero-extended to 64 bits, and writes `e w st` to `r`. `storeWord n a v` writes the
low `n` bytes of `v st` to the address `a st`. The functions `e` and `v` are the semantics of the
instruction: `add r8, [rdi + 8 rax]` is `loadReg 8 .r8 (sib 8 .rdi .rax 0) fun w st => w + st.regs.get64 .r8`. -/

def sib (k : Nat) (b i : Reg64) (d : Int64) (st : MachineData) : BitVec 64 :=
  st.regs.get64 b + st.regs.get64 i * BitVec.ofNat 64 k + BitVec.ofInt 64 d.toInt

def loadOk (n : Nat) (a : MachineData → BitVec 64) (st : MachineData) : Prop :=
  (Mem.loadInt st.dmem (a st) n).isSome = true

def storeOk (n : Nat) (a : MachineData → BitVec 64) (st : MachineData) : Prop :=
  loadOk n a st ∧ Mem.Blocks.Disjoint [(st.regs.get64 .rsp, 8)] [(a st, n)]

def word (n : Nat) (a : BitVec 64) (st : MachineData) : BitVec 64 :=
  BitVec.ofInt 64 ((Mem.loadInt st.dmem a n).get! % 2 ^ (8 * n))

def setReg64 (r : Reg64) (e : MachineData → BitVec 64) (st : MachineData) : MachineData :=
  { st with regs := st.regs.set64 r (e st) }

def loadReg (n : Nat) (r : Reg64) (a : MachineData → BitVec 64)
    (e : BitVec 64 → MachineData → BitVec 64) (st : MachineData) : MachineData :=
  { st with regs := st.regs.set64 r (e (word n (a st) st) st) }

def storeWord (n : Nat) (a v : MachineData → BitVec 64) (st : MachineData) : MachineData :=
  { st with dmem := Mem.storeInt st.dmem (a st) n (v st).toInt }

theorem sib_eight (b i : Reg64) (d : Int64) (st : MachineData) :
    sib 8 b i d st = st.regs.get64 b + st.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt := rfl

theorem sib_one (b i : Reg64) (d : Int64) (st : MachineData) :
    sib 1 b i d st = st.regs.get64 b + st.regs.get64 i + BitVec.ofInt 64 d.toInt := by
  simp only [sib, BitVec.mul_one]

theorem word_eight (a : BitVec 64) (st : MachineData) :
    word 8 a st = BitVec.ofInt 64 (Mem.loadInt st.dmem a 8).get! := by
  apply BitVec.eq_of_toNat_eq
  simp only [word, BitVec.toNat_ofInt]
  rw [Int.emod_emod_of_dvd _ (show ((2 ^ 64 : Nat) : Int) ∣ (2 : Int) ^ (8 * 8) from ⟨1, rfl⟩)]

section
variable (st : MachineData)

@[vcgen_simp] theorem setReg64_regs (r : Reg64) (e : MachineData → BitVec 64) :
    (setReg64 r e st).regs = st.regs.set64 r (e st) := rfl
@[vcgen_simp] theorem setReg64_dmem (r : Reg64) (e : MachineData → BitVec 64) :
    (setReg64 r e st).dmem = st.dmem := rfl
@[vcgen_simp] theorem setReg64_status (r : Reg64) (e : MachineData → BitVec 64) :
    (setReg64 r e st).status = st.status := rfl
@[vcgen_simp] theorem loadReg_regs (n : Nat) (r : Reg64) (a : MachineData → BitVec 64)
    (e : BitVec 64 → MachineData → BitVec 64) :
    (loadReg n r a e st).regs = st.regs.set64 r (e (word n (a st) st) st) := rfl
@[vcgen_simp] theorem loadReg_dmem (n : Nat) (r : Reg64) (a : MachineData → BitVec 64)
    (e : BitVec 64 → MachineData → BitVec 64) : (loadReg n r a e st).dmem = st.dmem := rfl
@[vcgen_simp] theorem storeWord_regs (n : Nat) (a v : MachineData → BitVec 64) :
    (storeWord n a v st).regs = st.regs := rfl
@[vcgen_simp] theorem storeWord_dmem (n : Nat) (a v : MachineData → BitVec 64) :
    (storeWord n a v st).dmem = Mem.storeInt st.dmem (a st) n (v st).toInt := rfl

end

theorem Mem.storeInt_one_take {w : Nat} (m : Mem w) (a : BitVec w) (x : BitVec 64) :
    Mem.storeInt m a 1 ((x.take 8).toInt) = Mem.storeInt m a 1 x.toInt := by
  unfold Mem.storeInt
  rw [← Int.toBytes_emod 1 ((x.take 8).toInt), ← Int.toBytes_emod 1 x.toInt]
  congr 2
  simp only [Int.take]
  rw [BitVec.toInt_emod_two_pow,
    ← Int.emod_emod_of_dvd x.toInt (show (2:Int) ^ (8 * 1) ∣ 2 ^ 64 from ⟨2 ^ 56, rfl⟩),
    BitVec.toInt_emod_two_pow]
  simp only [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

section
variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
open scoped Program.WP

theorem Spec.movzx_reg32_sib1 (r b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true ∧ Q () { s with regs := s.regs.set64 r (word 1 a s) } ⦄
      (Directive.instr (.regular .W64 .W32
          (@Operation.movzx .W32 .W8 (.reg (.low r .W32)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W32, AddrExpr.zeroExtend_interp_sib1,
    Width.bytes, hv, Effects.All]
  refine hn _ ?_
  have hw : word 1 (s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt) s
      = BitVec.zeroExtend 64 (BitVec.zeroExtend Width.W32.bits (BitVec.ofInt Width.W8.bits v)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [word, hv, Option.get!_some, BitVec.toNat_setWidth, BitVec.toNat_ofInt, Width.bits,
      Int.natCast_pow]
    omega
  rw [← hw]
  exact hq

theorem Spec.mov_sib1_reg8 (b i : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true
          ∧ Q () { s with dmem := Mem.storeInt s.dmem a 1 (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W8))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.store, Reg64s.get_low_W8, AddrExpr.zeroExtend_interp_sib1,
    Width.bytes, hv, Effects.All]
  rw [Mem.storeInt_one_take]
  exact hn _ hq

end

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
          (modifyIf (loadOk 8 (sib 8 b i d)) (loadReg 8 r (sib 8 b i d) fun w _ => w)) Q E :=
  by
  refine wrp_modifyIf (g := loadOk 8 (sib 8 b i d))
    (fun Q E s hp hq => (Program.WP.Spec.mov_reg_sib8 (Q := Q) (E := E) r b i d).le_wp s ⟨hp, hq⟩) ?_
  intro s hg
  exact ⟨hg, by rw [loadReg, word_eight]; rfl⟩

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
          (modifyIf (loadOk 8 (sib 8 b i d))
            (loadReg 8 rd (sib 8 b i d) fun w st => w + st.regs.get64 rd)) Q E :=
  by
  refine wrp_modifyIf (g := loadOk 8 (sib 8 b i d))
    (fun Q E s hp hq => (Program.WP.Spec.add_reg_sib8 (Q := Q) (E := E) rd b i d).le_wp s ⟨hp, hq⟩) ?_
  intro s hg
  exact ⟨hg, by rw [loadReg, word_eight]; rfl⟩

@[ascend] theorem wrp_movSib8Reg (b i : Reg64) (d : Int64) (rs : Reg64) :
    (fun s =>
      let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 8).isSome = true → Mem.Blocks.Disjoint [(s.regs.get64 .rsp, 8)] [(a, 8)] →
        Q () () { s with dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64
            (.mov (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W64))))))
          (modifyIf (storeOk 8 (sib 8 b i d)) (storeWord 8 (sib 8 b i d) fun st => st.regs.get64 rs)) Q E :=
  by
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf
    (g := storeOk 8 (sib 8 b i d))
    (fun Q E s hp hq => (Program.WP.Spec.mov_sib8_reg (Q := Q) (E := E) b i d rs).le_wp s ⟨hp, hq⟩)
    fun s hg => ⟨hg.1, rfl⟩)
  intro s h hg
  exact h hg.1 hg.2

@[ascend] theorem wrp_incReg (asz : Width) (r : Reg64) :
    (fun s => True → Q () () { s with
        regs := s.regs.set64 r (s.regs.get64 r + 1),
        status := StatusFlags.ofInc (s.regs.get64 r) s.status.cf })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz .W64 (.inc (.reg (.low r .W64)))))
          (modifyIf (fun _ => True) (setReg64 r fun st => st.regs.get64 r + 1)) Q E :=
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
          (modifyIf (fun _ => True) (setReg64 rd fun st =>
            ((st.regs.get64 rd).take 32 ^^^ (st.regs.get64 rs).take 32).zeroExtend 64)) Q E :=
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
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz .ret)) (exitIf (loadOk 8 fun st => st.regs.get64 .rsp)
        (setReg64 .rsp fun st => st.regs.get64 .rsp + 8) .exit) Q E :=
  by
  refine wrp_exitIf (pre := fun s => s.retAddr.isSome = true)
    (g := loadOk 8 fun st => st.regs.get64 .rsp)
    (fun Q E s hp he => (Program.WP.Spec.ret (Q := Q) (E := E) asz osz).le_wp s ⟨hp, he⟩) ?_ .exit
  intro s hg
  exact ⟨by simpa [MachineData.retAddr_eq, loadOk] using hg, rfl⟩

/-- A `ret` ends the block, and the directives after it are unreachable. -/
@[ascend default + 1] theorem wrp_ret_cons (asz osz : Width) (p : Program)
    (hN : Program.labels (Directive.instr (.regular asz osz .ret) :: p) = []) :
    (fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).isSome = true →
      E s.retAddr.get! .exit { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz .ret) :: p) (exitIf (loadOk 8 fun st => st.regs.get64 .rsp)
        (setReg64 .rsp fun st => st.regs.get64 .rsp + 8) .exit) Q E := by
  rw [← exitIf_bind _ _ .exit (fun _ => pure ())]
  exact PartialOrder.rel_trans (wrp_ret asz osz) (wrp_cons _ p _ (fun _ => pure ()) hN)

/-! ## Bytes, register moves, jumps, and flags carried to a later branch

`movzx r32, byte [b + i + d]` loads one byte with zero extension, and `mov byte [b + i + d], r8`
stores the low byte of a register. A flag that a branch reads is written by an earlier
instruction. `dec r` writes the flag `zf` as the test `r - 1 == 0`: the abstract program reads
that test with `peek` before the step, and a later `jcc` branches on the value. Between the two,
only instructions that leave the flags unchanged may run: their rules keep `status` of the state,
so the branch reads the flag that `dec` wrote. -/

@[ascend] theorem wrp_movzxRegSib1 (r b i : Reg64) (d : Int64) :
    (fun s =>
      let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 1).isSome = true → Q () () { s with regs := s.regs.set64 r (word 1 a s) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W32
            (@Operation.movzx .W32 .W8 (.reg (.low r .W32)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))))
          (modifyIf (loadOk 1 (sib 1 b i d)) (loadReg 1 r (sib 1 b i d) fun w _ => w)) Q E := by
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf (g := loadOk 1 (sib 1 b i d))
    (fun Q E s hp hq => (Spec.movzx_reg32_sib1 (Q := Q) (E := E) r b i d).le_wp s ⟨hp, hq⟩)
    fun s hg => ⟨by simpa only [loadOk, sib_one, abs_regs, abs_dmem] using hg, by simp only [abs, loadReg, sib_one, word]⟩)
  intro s h hg
  exact h (by simpa only [loadOk, sib_one, abs_regs, abs_dmem] using hg)

@[ascend] theorem wrp_movSib1Reg8 (b i : Reg64) (d : Int64) (rs : Reg64) :
    (fun s =>
      let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 1).isSome = true → Mem.Blocks.Disjoint [(s.regs.get64 .rsp, 8)] [(a, 1)] →
        Q () () { s with dmem := Mem.storeInt s.dmem a 1 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W8
            (.mov (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W8))))))
          (modifyIf (storeOk 1 (sib 1 b i d)) (storeWord 1 (sib 1 b i d) fun st => st.regs.get64 rs)) Q E := by
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf
    (g := storeOk 1 (sib 1 b i d))
    (fun Q E s hp hq => (Spec.mov_sib1_reg8 (Q := Q) (E := E) b i d rs).le_wp s ⟨hp, hq⟩)
    fun s hg => ⟨by simpa only [storeOk, loadOk, sib_one, abs_regs, abs_dmem] using hg.1,
      by simp only [abs, storeWord, sib_one]⟩)
  intro s h hg
  simp only [storeOk, loadOk, sib_one, abs_regs, abs_dmem] at hg
  simpa only [sib_one] using h hg.1 hg.2

@[ascend] theorem wrp_movRegReg (asz : Width) (rd rs : Reg64) :
    (fun s => True → Q () () { s with regs := s.regs.set64 rd (s.regs.get64 rs) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64 (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
          (modifyIf (fun _ => True) (setReg64 rd fun st => st.regs.get64 rs)) Q E := by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.mov_reg_reg (Q := Q) (E := E) asz rd rs).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_jmp (asz osz : Width) (l : Label) :
    (fun s => E (label l) (.label l) s)
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction)))))
          (branch (fun _ => true) (.label l)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_branch, ↓reduceIte] at hs
  refine (Program.WP.Spec.jmp_label asz osz l).le_wp s ?_
  show (ofStateRepr abs).post E Ea.1 (label l) s
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
    ofStateRepr_pred]
  exact ⟨.label l, hs.1, hs.2⟩

/-- A `jmp` ends the block, and the directives after it are unreachable. -/
@[ascend default + 1] theorem wrp_jmp_cons (asz osz : Width) (l : Label) (p : Program)
    (hN : Program.labels (Directive.instr (.regular asz osz
      (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p) = []) :
    (fun s => E (label l) (.label l) s)
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p)
          (branch (fun _ => true) (.label l)) Q E := by
  rw [← bind_pure_unit (x := (branch (fun _ => true) (.label l) : BlockM MachineData Unit))]
  exact PartialOrder.rel_trans (wrp_jmp asz osz l) (wrp_cons _ p _ (fun _ => pure ()) hN)

@[ascend] theorem wrp_jcc (asz osz : Width) (cc : CondCode) (l : Label) (b : Bool) :
    (fun s => PureRefinement (cc.interp s.status) b True Eq ∧
      (b = true → E (label l) (.label l) s) ∧ (b = false → Q () () s))
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz (.jcc cc l)))
          (branch (fun _ => b) (.label l)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_branch] at hs
  obtain ⟨⟨hb, hjmp, hfall⟩, hw⟩ := hs
  have hc : cc.interp s.status = b := hb trivial
  refine (Program.WP.Spec.jcc_label asz osz cc l).le_wp s ⟨fun h => ?_, fun h => ?_⟩
  · rw [hc] at h
    simp only [h, ↓reduceIte] at hw
    show (ofStateRepr abs).post E Ea.1 (label l) s
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
      ofStateRepr_pred]
    exact ⟨.label l, hjmp h, hw⟩
  · rw [hc] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
    show (ofStateRepr abs).post Q Qa () s
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
      ofStateRepr_pred]
    exact ⟨(), hfall h, hw⟩

@[ascend] theorem wrp_decReg (asz : Width) (r : Reg64) {Qb : Unit → Bool → MachineData → Prop} :
    (fun s => ∀ (cf z : Bool), PureRefinement (s.regs.get64 r - 1 == BitVec.zero 64) z True Eq →
      Qb () z { s with regs := s.regs.set64 r (s.regs.get64 r - 1), status := StatusFlags.ofDec (s.regs.get64 r) cf })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz .W64 (.dec (.reg (.low r .W64)))))
          (do
            let z ← peek fun (st : MachineData) => st.regs.get64 r - 1 == BitVec.zero 64
            modifyIf (fun _ => True) (setReg64 r fun st => st.regs.get64 r - 1)
            pure z : BlockM MachineData Bool) Qb E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq, wp_peek,
    wp_modifyIf, WPMonadExact.wp_pure_eq] at hs
  obtain ⟨hk, -, hw⟩ := hs
  refine (Program.WP.Spec.dec_reg asz r).le_wp s ?_
  show (ofStateRepr abs).post Qb Qa () _
  rw [Concretization.post_pi]
  exact ⟨_, hk s.status.cf _ (PureRefinement.of_rel rfl), hw⟩

omit [Host] [FunDecls] in
@[ascend_pure] theorem abs_interp_nz {st : StatusFlags} {z : Bool} {P : Prop}
    (h : PureRefinement st.zf z P Eq) : PureRefinement (CondCode.nz.interp st) (!z) P Eq :=
  fun hp => by rw [CondCode.interp_nz, h hp]

omit [Host] [FunDecls] in
@[ascend_pure] theorem abs_interp_z {st : StatusFlags} {z : Bool} {P : Prop}
    (h : PureRefinement st.zf z P Eq) : PureRefinement (CondCode.z.interp st) z P Eq :=
  fun hp => by rw [CondCode.interp_z, h hp]


end

end AInstr

end Ascent.Kraken
