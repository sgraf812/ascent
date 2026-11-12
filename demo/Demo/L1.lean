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
guard `g` holds and is undefined behaviour otherwise, `exitIf g f a` updates and throws the address
`a`, and `branch st c a` throws `a` when the condition `c` holds, in a state with the stack test
`st`. The operations in `AInstr` name one such step per machine instruction, and each `@[ascend]`
rule pairs it with kraken's spec of that instruction. The update of a step is the post state of the
spec, and a guard is the precondition of the spec stated on the abstract state.

The rules of a jump and of a return read the frame from the exit relation `AddrRel r₀ ra₀`: the
stack pointer `r₀` and the return address `ra₀` of the entry state. A jump to the label `l` throws
`label l` and assumes the stack test of `r₀`. A return assumes `retOk r₀ ra₀`: the stack pointer is
`r₀` and the return slot holds `ra₀`. It sets the stack pointer to `r₀ + 8` and throws `ra₀`.
-/

open Std.WP Lean.Order Ascent
open Ascent.Concretization (ofStateRepr ofStateRepr_pred ofStateRel ofStateRel_pred)
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

theorem CondCode.cmp_z_eq_true (a b : BitVec 64) : (CondCode.z.cmp a b = true) = (a = b) := by
  simp [CondCode.cmp]

theorem CondCode.cmp_nc_eq_true (a b : BitVec 64) : (CondCode.nc.cmp a b = true) = (b ≤ a) := by
  simp [CondCode.cmp, BitVec.ule_eq_decide, BitVec.le_def]

theorem CondCode.cmp_be_eq_true (a b : BitVec 64) : (CondCode.be.cmp a b = true) = (a ≤ b) := by
  simp [CondCode.cmp, BitVec.ule_eq_decide, BitVec.le_def]

theorem CondCode.cmp_l_eq_true (a b : BitVec 64) : (CondCode.l.cmp a b = true) = (a.toInt < b.toInt) := by
  simp [CondCode.cmp, BitVec.slt_iff_toInt_lt]

theorem add_ofInt_neg_one (x : BitVec 64) : x + BitVec.ofInt 64 (-1 : Int64).toInt = x - 1#64 :=
  (BitVec.sub_eq_add_neg x 1#64).symm

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

/-! ## Memory relations -/

/-- The memory `m` is a sub-map of `m'`. -/
def Mem.Sub (m m' : DataMem) : Prop := ∀ p v, m.get? p = some v → m'.get? p = some v

theorem Mem.Sub.refl (m : DataMem) : Mem.Sub m m := fun _ _ h => h

theorem Mem.Sub.storeInt {m m' : DataMem} (h : Mem.Sub m m') (a : BitVec 64) (n : Nat) (v : Int) :
    Mem.Sub (m.storeInt a n v) (m'.storeInt a n v) := fun p x hp => by
  rw [Mem.get?_storeInt] at hp ⊢
  cases hb : ((Int.toBytes n v).At a)[p]? with
  | some y => rw [hb] at hp; exact hp
  | none => rw [hb] at hp; exact h p x hp

theorem Mem.Sub.loadBytes {m m' : DataMem} (h : Mem.Sub m m') {a : BitVec 64} {n : Nat}
    {bs : List UInt8} (hl : m.loadBytes a n = some bs) : m'.loadBytes a n = some bs := by
  rw [Mem.loadBytes_eq_some_iff] at hl ⊢
  exact ⟨hl.1, fun i hi => h _ _ (hl.2 i hi)⟩

theorem Mem.Sub.loadInt {m m' : DataMem} (h : Mem.Sub m m') {a : BitVec 64} {n : Nat} {v : Int}
    (hl : m.loadInt a n = some v) : m'.loadInt a n = some v := by
  simp only [Mem.loadInt, Option.map_eq_some_iff] at hl ⊢
  obtain ⟨bs, hbs, rfl⟩ := hl
  exact ⟨bs, h.loadBytes hbs, rfl⟩

theorem Mem.Sub.loadInt_isSome {m m' : DataMem} (h : Mem.Sub m m') {a : BitVec 64} {n : Nat}
    (hl : (m.loadInt a n).isSome = true) : (m'.loadInt a n).isSome = true := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
  rw [h.loadInt hv]
  rfl

theorem Mem.Sub.loadInt_get! {m m' : DataMem} (h : Mem.Sub m m') {a : BitVec 64} {n : Nat}
    (hl : (m.loadInt a n).isSome = true) : (m.loadInt a n).get! = (m'.loadInt a n).get! := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
  rw [hv, h.loadInt hv]

/-- A relation between memories that the step rules support: it is a sub-map relation and stores
keep it. -/
class MemRel (M : DataMem → DataMem → Prop) : Prop where
  sub : ∀ {m m'}, M m m' → Mem.Sub m m'
  store : ∀ {m m'}, M m m' → ∀ a n v, (m.loadInt a n).isSome = true → M (m.storeInt a n v) (m'.storeInt a n v)

instance : MemRel (Eq : DataMem → DataMem → Prop) where
  sub h := h ▸ Mem.Sub.refl _
  store h _ _ _ _ := h ▸ rfl

instance : MemRel Mem.Sub where
  sub h := h
  store h a n v _ := h.storeInt a n v

/-- `m` is a sub-map of `m'` that lacks the cells of `P`, the return slots of the active frames, and
`m'` holds the values of `P` in them. -/
def Mem.SubSlots (P m m' : DataMem) : Prop :=
  Mem.Sub m m' ∧ ∀ p v, P.get? p = some v → m'.get? p = some v ∧ m.get? p = none

theorem Mem.get?_isSome_of_loadInt {m : DataMem} {a : BitVec 64} {n : Nat} (h : (m.loadInt a n).isSome = true)
    {i : Nat} (hi : i < n) : (m.get? (a + BitVec.ofNat 64 i)).isSome = true := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  simp only [Mem.loadInt, Option.map_eq_some_iff] at hv
  obtain ⟨bs, hbs, -⟩ := hv
  obtain ⟨hl, hb⟩ := Mem.loadBytes_eq_some_iff.mp hbs
  rw [hb i (by omega)]
  rfl

instance {P : DataMem} : MemRel (Mem.SubSlots P) where
  sub h := h.1
  store h a n v hm := by
    refine ⟨h.1.storeInt a n v, fun p x hp => ?_⟩
    obtain ⟨h₁, h₂⟩ := h.2 p x hp
    have hn : ((Int.toBytes n v).At a)[p]? = none := by
      apply Std.ExtHashMap.getElem?_eq_none
      intro hmem
      obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hmem
      rw [Int.toBytes_length] at hi
      have := Mem.get?_isSome_of_loadInt hm hi
      rw [h₂] at this
      exact nomatch this
    rw [Mem.get?_storeInt, Mem.get?_storeInt, hn]
    exact ⟨h₁, h₂⟩

/-- The abstract states `a` and `b` agree on the registers and the flags, and their memories are
related by `M`. -/
def StRel (M : DataMem → DataMem → Prop) (a b : MachineData) : Prop :=
  a.regs = b.regs ∧ a.zmms = b.zmms ∧ a.status = b.status ∧ M a.dmem b.dmem

/-- The concrete state `s` and an abstract state related to `abs s` by `StRel M`. -/
def JRel (M : DataMem → DataMem → Prop) (s a : MachineData) : Prop := StRel M a (abs s)

theorem jrel_eq_iff (s a : MachineData) : JRel Eq s a ↔ a = abs s := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    cases a
    simp only [abs] at h₁ h₂ h₃ h₄ ⊢
    subst h₁ h₂ h₃ h₄
    rfl
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem ofStateRepr_abs_eq : ofStateRepr abs = ofStateRel (JRel Eq) := by
  rw [ofStateRepr_eq_ofStateRel]
  congr 1
  funext s a
  exact propext (jrel_eq_iff s a).symm

theorem JRel.regs {M} {s a : MachineData} (h : JRel M s a) : a.regs = s.regs := h.1

namespace AInstr

/-! ## The generic rules -/

section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}
  {E : Int64 → Int64 → MachineData → Prop}

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
    (hsim : ∀ s, g (abs s) → pre s ∧ abs (upd s) = f (abs s)) (l : Int64) :
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
is the same: the bytes are mapped.

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
  loadOk n a st

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

theorem Mem.storeInt_take {w : Nat} (m : Mem w) (a : BitVec w) (n k : Nat) (h : n ≤ 8) (hk : k = 8 * n)
    (x : BitVec 64) : Mem.storeInt m a n ((x.take k).toInt) = Mem.storeInt m a n x.toInt := by
  subst hk
  unfold Mem.storeInt
  rw [← Int.toBytes_emod n ((x.take (8 * n)).toInt), ← Int.toBytes_emod n x.toInt]
  congr 2
  have hd : (2:Int) ^ (8 * n) ∣ 2 ^ 64 := ⟨2 ^ (64 - 8 * n), by rw [← Int.pow_add]; congr 1; omega⟩
  simp only [Int.take]
  rw [BitVec.toInt_emod_two_pow, ← Int.emod_emod_of_dvd x.toInt hd, BitVec.toInt_emod_two_pow]
  simp only [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  push_cast
  rfl

theorem word_setWidth (n k : Nat) (h : n ≤ 8) (hk : k = 8 * n) (a : BitVec 64) (st : MachineData) :
    (word n a st).setWidth k = BitVec.ofInt k (Mem.loadInt st.dmem a n).get! := by
  subst hk
  apply BitVec.eq_of_toNat_eq
  have hd : (2:Nat) ^ (8 * n) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [word, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  generalize (Mem.loadInt st.dmem a n).get! = v
  rw [show (2 : Int) ^ (8 * n) = ((2 ^ (8 * n) : Nat) : Int) by push_cast; rfl]
  generalize hc : 2 ^ (8 * n) = c at *
  have hp : 0 < c := hc ▸ Nat.pow_pos (by omega)
  have h0 := Int.emod_nonneg v (show (c : Int) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos v (show (0 : Int) < c by omega)
  rw [Int.emod_eq_of_lt h0 (by omega), Nat.mod_eq_of_lt (by omega)]

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
  rw [Mem.storeInt_take _ _ 1 8 (by omega) rfl]
  exact hn _ hq

end

/-! ## The rules of the example -/

section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}
  {E : Int64 → Int64 → MachineData → Prop}

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
      (Mem.loadInt s.dmem a 8).isSome = true →
        Q () () { s with dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64
            (.mov (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W64))))))
          (modifyIf (storeOk 8 (sib 8 b i d)) (storeWord 8 (sib 8 b i d) fun st => st.regs.get64 rs)) Q E :=
  by
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf
    (g := storeOk 8 (sib 8 b i d))
    (fun Q E s hp hq => (Program.WP.Spec.mov_sib8_reg (Q := Q) (E := E) b i d rs).le_wp s ⟨hp, hq⟩)
    fun s hg => ⟨hg, rfl⟩)
  intro s h hg
  exact h hg

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
@[ascend default + 1] theorem wrp_cmpJcc_rel {M : DataMem → DataMem → Prop} {r₀ : BitVec 64} {ra₀ : Int64} (asz₁ asz₂ osz : Width) (ra rb : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s =>
      let s' := { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) }
      (cc.cmp (s.regs.get64 ra) (s.regs.get64 rb) = true → (AddrRel r₀ ra₀) (label l) (label l) s')
        ∧ (cc.cmp (s.regs.get64 ra) (s.regs.get64 rb) = false → wrp (ofStateRel (JRel M)) p (k ()) Q (AddrRel r₀ ra₀) s'))
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz₁ .W64
              (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (branch (stayIn (r₀)) (fun st => cc.cmp (st.regs.get64 ra) (st.regs.get64 rb)) (label l) >>= k) Q (AddrRel r₀ ra₀) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, WPMonadExact.wp_bind_eq,
    wp_branch] at hs
  obtain ⟨⟨hjmp, hfall⟩, a, hJ, hw⟩ := hs
  rw [JRel.regs hJ] at hw
  have h₂ : wp (Directive.instr (.regular asz₂ osz (.jcc cc l)))
      (fun _ => wp p ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea)
      { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) } := by
    refine (Program.WP.Spec.jcc_label asz₂ osz cc l).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, ↓reduceIte] at hw
      show (ofStateRel (JRel M)).post (AddrRel r₀ ra₀) Ea.1 (label l) _
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, ofStateRel_pred]
      exact ⟨label l, hjmp h, a, hJ, hw.2⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      refine wrp_transport (P := wrp (ofStateRel (JRel M)) p (k ()) Q (AddrRel r₀ ra₀)) PartialOrder.rel_refl Qa Ea _ ?_
      simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
      exact ⟨hfall h, a, hJ, hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W64
        (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea) s :=
    (Program.WP.Spec.cmp_reg_reg asz₁ ra rb).le_wp s (Program.wp_cons hN h₂)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN) h₁

@[ascend default + 1] theorem wrp_cmpJcc {r₀ : BitVec 64} {ra₀ : Int64} (asz₁ asz₂ osz : Width) (ra rb : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s =>
      let s' := { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) }
      (cc.cmp (s.regs.get64 ra) (s.regs.get64 rb) = true → (AddrRel r₀ ra₀) (label l) (label l) s')
        ∧ (cc.cmp (s.regs.get64 ra) (s.regs.get64 rb) = false → wrp (ofStateRepr abs) p (k ()) Q (AddrRel r₀ ra₀) s'))
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz₁ .W64
              (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (branch (stayIn (r₀)) (fun st => cc.cmp (st.regs.get64 ra) (st.regs.get64 rb)) (label l) >>= k) Q (AddrRel r₀ ra₀) := by
  rw [ofStateRepr_abs_eq]
  exact wrp_cmpJcc_rel asz₁ asz₂ osz ra rb cc l p k hN

/-- `test ra, rb; jcc cc, l` branches on the comparison of `ra &&& rb` with zero. -/
@[ascend default + 1] theorem wrp_testJcc_rel {M : DataMem → DataMem → Prop} {r₀ : BitVec 64} {ra₀ : Int64} (asz₁ asz₂ osz : Width) (ra rb : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s => ∀ af : Bool,
      let s' := { s with status := StatusFlags.ofLogic (s.regs.get64 ra &&& s.regs.get64 rb) af }
      (cc.cmp (s.regs.get64 ra &&& s.regs.get64 rb) 0 = true → (AddrRel r₀ ra₀) (label l) (label l) s')
        ∧ (cc.cmp (s.regs.get64 ra &&& s.regs.get64 rb) 0 = false →
            wrp (ofStateRel (JRel M)) p (k ()) Q (AddrRel r₀ ra₀) s'))
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz₁ .W64
              (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (branch (stayIn (r₀)) (fun st => cc.cmp (st.regs.get64 ra &&& st.regs.get64 rb) 0) (label l) >>= k) Q (AddrRel r₀ ra₀) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, WPMonadExact.wp_bind_eq,
    wp_branch] at hs
  obtain ⟨hpre, a, hJ, hw⟩ := hs
  rw [JRel.regs hJ] at hw
  have h₂ : ∀ af : Bool, wp (Directive.instr (.regular asz₂ osz (.jcc cc l)))
      (fun _ => wp p ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea)
      { s with status := StatusFlags.ofLogic (s.regs.get64 ra &&& s.regs.get64 rb) af } := by
    intro af
    obtain ⟨hjmp, hfall⟩ := hpre af
    refine (Program.WP.Spec.jcc_label asz₂ osz cc l).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_ofLogic] at h
      simp only [h, ↓reduceIte] at hw
      show (ofStateRel (JRel M)).post (AddrRel r₀ ra₀) Ea.1 (label l) _
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, ofStateRel_pred]
      exact ⟨label l, hjmp h, a, hJ, hw.2⟩
    · rw [CondCode.interp_ofLogic] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      refine wrp_transport (P := wrp (ofStateRel (JRel M)) p (k ()) Q (AddrRel r₀ ra₀)) PartialOrder.rel_refl Qa Ea _ ?_
      simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
      exact ⟨hfall h, a, hJ, hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W64
        (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea) s :=
    (Program.WP.Spec.test_reg_reg asz₁ ra rb).le_wp s fun af => Program.wp_cons hN (h₂ af)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN) h₁

@[ascend default + 1] theorem wrp_testJcc {r₀ : BitVec 64} {ra₀ : Int64} (asz₁ asz₂ osz : Width) (ra rb : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s => ∀ af : Bool,
      let s' := { s with status := StatusFlags.ofLogic (s.regs.get64 ra &&& s.regs.get64 rb) af }
      (cc.cmp (s.regs.get64 ra &&& s.regs.get64 rb) 0 = true → (AddrRel r₀ ra₀) (label l) (label l) s')
        ∧ (cc.cmp (s.regs.get64 ra &&& s.regs.get64 rb) 0 = false →
            wrp (ofStateRepr abs) p (k ()) Q (AddrRel r₀ ra₀) s'))
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz₁ .W64
              (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (branch (stayIn (r₀)) (fun st => cc.cmp (st.regs.get64 ra &&& st.regs.get64 rb) 0) (label l) >>= k) Q (AddrRel r₀ ra₀) := by
  rw [ofStateRepr_abs_eq]
  exact wrp_testJcc_rel asz₁ asz₂ osz ra rb cc l p k hN

/-- The guard of a return from the frame `r₀`: the stack pointer is `r₀` and the return slot holds
`ra`. -/
def retOk (r₀ : BitVec 64) (ra : Int64) (st : MachineData) : Prop :=
  st.regs.get64 .rsp = r₀ ∧ st.retAddr = some ra

@[ascend] theorem wrp_ret {r₀ : BitVec 64} {ra₀ : Int64} (asz osz : Width) :
    (fun _ => True)
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz .ret))
        (exitIf (retOk r₀ ra₀) (setReg64 .rsp fun _ => r₀ + 8) ra₀)
        Q (AddrRel r₀ ra₀) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_exitIf] at hs
  obtain ⟨-, ⟨hr, ha⟩, hE⟩ := hs
  simp only [abs_regs] at hr
  have ha : s.retAddr = some ra₀ := by
    simpa [MachineData.retAddr_eq] using ha
  refine (Program.WP.Spec.ret asz osz).le_wp s ⟨by rw [ha]; rfl, ?_⟩
  · show (ofStateRepr abs).post (AddrRel r₀ ra₀) Ea.1 _ _
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
      ofStateRepr_pred, AddrRel]
    refine ⟨ra₀, ?_, ?_⟩
    · rw [ha]; rfl
    · have hs' : abs { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) }
          = setReg64 .rsp (fun _ => r₀ + 8) (abs s) := by
        rw [hr]
        rfl
      rw [hs']
      exact hE

/-- A `ret` ends the block, and the directives after it are unreachable. -/
@[ascend default + 1] theorem wrp_ret_cons {r₀ : BitVec 64} {ra₀ : Int64} (asz osz : Width) (p : Program)
    (hN : Program.labels (Directive.instr (.regular asz osz .ret) :: p) = []) :
    (fun _ => True)
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz .ret) :: p)
        (exitIf (retOk r₀ ra₀) (setReg64 .rsp fun _ => r₀ + 8) ra₀)
        Q (AddrRel r₀ ra₀) := by
  rw [← exitIf_bind _ _ _ (fun _ => pure ())]
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
      (Mem.loadInt s.dmem a 1).isSome = true →
        Q () () { s with dmem := Mem.storeInt s.dmem a 1 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W8
            (.mov (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W8))))))
          (modifyIf (storeOk 1 (sib 1 b i d)) (storeWord 1 (sib 1 b i d) fun st => st.regs.get64 rs)) Q E := by
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf
    (g := storeOk 1 (sib 1 b i d))
    (fun Q E s hp hq => (Spec.mov_sib1_reg8 (Q := Q) (E := E) b i d rs).le_wp s ⟨hp, hq⟩)
    fun s hg => ⟨by simpa only [storeOk, loadOk, sib_one, abs_regs, abs_dmem] using hg,
      by simp only [abs, storeWord, sib_one]⟩)
  intro s h hg
  simp only [storeOk, loadOk, sib_one, abs_regs, abs_dmem] at hg
  simpa only [sib_one] using h hg

@[ascend] theorem wrp_movRegReg (asz : Width) (rd rs : Reg64) :
    (fun s => True → Q () () { s with regs := s.regs.set64 rd (s.regs.get64 rs) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64 (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
          (modifyIf (fun _ => True) (setReg64 rd fun st => st.regs.get64 rs)) Q E := by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.mov_reg_reg (Q := Q) (E := E) asz rd rs).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_jmp {r₀ : BitVec 64} {ra₀ : Int64} (asz osz : Width) (l : Label) :
    (fun s => (AddrRel r₀ ra₀) (label l) (label l) s)
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction)))))
          (branch (stayIn (r₀)) (fun _ => true) (label l)) Q (AddrRel r₀ ra₀) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_branch, ↓reduceIte] at hs
  refine (Program.WP.Spec.jmp_label asz osz l).le_wp s ?_
  show (ofStateRepr abs).post (AddrRel r₀ ra₀) Ea.1 (label l) s
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
    ofStateRepr_pred]
  exact ⟨label l, hs.1, hs.2.2⟩

/-- A `jmp` ends the block, and the directives after it are unreachable. -/
@[ascend default + 1] theorem wrp_jmp_cons {r₀ : BitVec 64} {ra₀ : Int64} (asz osz : Width) (l : Label) (p : Program)
    (hN : Program.labels (Directive.instr (.regular asz osz
      (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p) = []) :
    (fun s => (AddrRel r₀ ra₀) (label l) (label l) s)
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p)
          (branch (stayIn (r₀)) (fun _ => true) (label l)) Q (AddrRel r₀ ra₀) := by
  rw [← bind_pure_unit (x := (branch (stayIn (r₀)) (fun _ => true) (label l) : BlockM MachineData Unit))]
  exact PartialOrder.rel_trans (wrp_jmp asz osz l) (wrp_cons _ p _ (fun _ => pure ()) hN)

@[ascend] theorem wrp_jcc {r₀ : BitVec 64} {ra₀ : Int64} (asz osz : Width) (cc : CondCode) (l : Label) (b : Bool) :
    (fun s => PureRefinement (cc.interp s.status) b True Eq ∧
      (b = true → (AddrRel r₀ ra₀) (label l) (label l) s) ∧ (b = false → Q () () s))
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular asz osz (.jcc cc l)))
          (branch (stayIn (r₀)) (fun _ => b) (label l)) Q (AddrRel r₀ ra₀) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_branch] at hs
  obtain ⟨⟨hb, hjmp, hfall⟩, hw⟩ := hs
  have hc : cc.interp s.status = b := hb trivial
  refine (Program.WP.Spec.jcc_label asz osz cc l).le_wp s ⟨fun h => ?_, fun h => ?_⟩
  · rw [hc] at h
    simp only [h, ↓reduceIte] at hw
    show (ofStateRepr abs).post (AddrRel r₀ ra₀) Ea.1 (label l) s
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and,
      ofStateRepr_pred]
    exact ⟨label l, hjmp h, hw.2⟩
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

/-! ## Subtraction, shifts, byte writes and byte tests, and a comparison read by two jumps

`sub rd, rs; jcc` writes the difference and branches on the comparison of the values before the
write: the abstract program reads the comparison with `peek` before the write. `cmp; jcc; jcc`
branches twice on one comparison, since a jump that is not taken leaves the flags unchanged. A test
of two byte registers branches on the flags of the byte `ra8 &&& rb8`. -/

namespace Ascent.Kraken.AInstr

section
variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
open scoped Program.WP

local macro "run_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
      Reg64s.get_low_W64, Reg64s.set_low_W64, Reg64s.get_low_W8, Reg64s.set_low_W8, Effects.All,
      ite_true, ShiftCountExpr.interpMasked, ShiftCountExpr.interp])

theorem Spec.sub_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status := StatusFlags.ofSub (s.regs.get64 rd) (s.regs.get64 rs) } ⦄
      (Directive.instr (.regular asz .W64 (.sub (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_step; exact hn _ hq

theorem Spec.shr_reg_one (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ af : Bool, Q () { s with regs := s.regs.set64 r ((s.regs.get64 r).ushiftRight 1), status := StatusFlags.from_result ((s.regs.get64 r).ushiftRight 1) { cf := (s.regs.get64 r).getLsbD 0, af := af, of := (s.regs.get64 r).msb } } ⦄
      (Directive.instr (.regular asz .W64 (.shr (.reg (.low r .W64)) (.imm8 (.int64 1)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    have h1 : ((Int64.toBitVec 1).take 8).toNat &&& 63 = 1 := rfl
    simp only [h1, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, Width.bits, Nat.reduceLT, Nat.reduceSub,
      beq_self_eq_true, Nat.sub_self]
    intro af
    exact hn _ (hq af)

theorem Spec.mov_reg8_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (i.toBitVec.truncate 8)) } ⦄
      (Directive.instr (.regular asz .W8 (.mov (.reg (.low r .W8)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_step; exact hn _ hq

theorem Spec.test_reg8_reg8 (asz : Width) (ra rb : Reg64) :
    ⦃ fun s => ∀ af : Bool, Q () { s with status := StatusFlags.from_result ((s.regs.get64 ra).take 8 &&& (s.regs.get64 rb).take 8) { cf := false, af := af, of := false } } ⦄
      (Directive.instr (.regular asz .W8 (.test (.reg (.low ra .W8)) (.regOrMem (.reg (.low rb .W8))))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    intro af
    exact hn _ (hq af)

end
end Ascent.Kraken.AInstr

namespace Ascent.Kraken.AInstr
section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}
  {E : Int64 → Int64 → MachineData → Prop}
open scoped Program.WP

@[ascend] theorem wrp_movRegImm (asz : Width) (r : Reg64) (i : Int64) :
    (fun s => True → Q () () { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))))
          (modifyIf (fun _ => True) (setReg64 r fun _ => BitVec.setWidth 64 i.toBitVec)) Q E := by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.mov_reg_imm (Q := Q) (E := E) asz r i).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_movReg8Imm (asz : Width) (r : Reg64) (i : Int64) :
    (fun s => True → Q () ()
        { s with regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (i.toBitVec.truncate 8)) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W8 (.mov (.reg (.low r .W8)) (.imm (.int64 i)))))
          (modifyIf (fun _ => True)
            (setReg64 r fun st => (st.regs.get64 r).replaceLow (i.toBitVec.truncate 8))) Q E := by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Spec.mov_reg8_imm (Q := Q) (E := E) asz r i).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_addRegReg (asz : Width) (rd rs : Reg64) :
    (fun s => True → Q () () { s with
        regs := s.regs.set64 rd (s.regs.get64 rs + s.regs.get64 rd),
        status := StatusFlags.ofAdd (s.regs.get64 rs) (s.regs.get64 rd) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64 (.add (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
          (modifyIf (fun _ => True) (setReg64 rd fun st => st.regs.get64 rs + st.regs.get64 rd)) Q E := by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.add_reg_reg (Q := Q) (E := E) asz rd rs).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_shrRegOne (asz : Width) (r : Reg64) :
    (fun s => True → ∀ af : Bool, Q () () { s with
        regs := s.regs.set64 r ((s.regs.get64 r).ushiftRight 1),
        status := StatusFlags.from_result ((s.regs.get64 r).ushiftRight 1)
          { cf := (s.regs.get64 r).getLsbD 0, af := af, of := (s.regs.get64 r).msb } })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64 (.shr (.reg (.low r .W64)) (.imm8 (.int64 1)))))
          (modifyIf (fun _ => True) (setReg64 r fun st => (st.regs.get64 r).ushiftRight 1)) Q E := by
  refine wrp_modifyIf_forall (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Spec.shr_reg_one (Q := Q) (E := E) asz r).le_wp s hq)
    (fun _ _ => trivial) ?_
  intro s af _
  rfl

end
end Ascent.Kraken.AInstr

namespace Ascent.Kraken.AInstr
section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}
  {E : Int64 → Int64 → MachineData → Prop}
open scoped Program.WP

omit [Host] [FunDecls] in
theorem CondCode.z_interp_from_result {w : Nat} (v : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result v f) = (v == 0#w) := rfl

omit [Host] [FunDecls] in
theorem _root_.Reg64s.get64_set64_eq (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).get64 r = v := by
  simp

omit [Host] [FunDecls] in
theorem _root_.BitVec.take_eq_setWidth {w : Nat} (x : BitVec w) (n : Nat) : x.take n = x.setWidth n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.take, hi]

omit [Host] [FunDecls] in
theorem _root_.BitVec.setWidth_replaceLow_8 (x : BitVec 64) (v : BitVec 8) : (x.replaceLow v).setWidth 8 = v := by
  rw [← BitVec.take_eq_setWidth]; exact BitVec.take_replaceLow_8 x v

theorem CondCode.interp_from_result_af {w : Nat} (cc : CondCode) (v : BitVec w) (cf af of : Bool) :
    cc.interp (StatusFlags.from_result v { cf, af, of })
      = cc.interp (StatusFlags.from_result v { cf, af := false, of }) := by
  cases cc <;> rfl

/-- `sub rd, rs; jcc cc, l` writes the difference and branches on the comparison of the two
values before the write, which the abstract program reads with `peek`. -/
@[ascend default + 1] theorem wrp_subJcc_rel {M : DataMem → DataMem → Prop} {r₀ : BitVec 64} {ra₀ : Int64} (asz₁ asz₂ osz : Width) (rd rs : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s =>
      let s' := { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status := StatusFlags.ofSub (s.regs.get64 rd) (s.regs.get64 rs) }
      (cc.cmp (s.regs.get64 rd) (s.regs.get64 rs) = true → (AddrRel r₀ ra₀) (label l) (label l) s')
        ∧ (cc.cmp (s.regs.get64 rd) (s.regs.get64 rs) = false → wrp (ofStateRel (JRel M)) p (k ()) Q (AddrRel r₀ ra₀) s'))
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz₁ .W64
              (.sub (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (peek (fun st => cc.cmp (st.regs.get64 rd) (st.regs.get64 rs)) >>= fun c =>
            modifyIf (fun _ => True) (setReg64 rd fun st => st.regs.get64 rd - st.regs.get64 rs) >>= fun _ =>
            branch (stayIn (r₀)) (fun _ => c) (label l) >>= k) Q (AddrRel r₀ ra₀) := by
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
      (fun _ => wp p ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea)
      { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status := StatusFlags.ofSub (s.regs.get64 rd) (s.regs.get64 rs) } := by
    refine (Program.WP.Spec.jcc_label asz₂ osz cc l).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, ↓reduceIte] at hw
      show (ofStateRel (JRel M)).post (AddrRel r₀ ra₀) Ea.1 (label l) _
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, ofStateRel_pred]
      exact ⟨label l, hjmp h, _, hJ', hw.2⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      refine wrp_transport (P := wrp (ofStateRel (JRel M)) p (k ()) Q (AddrRel r₀ ra₀)) PartialOrder.rel_refl Qa Ea _ ?_
      simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
      exact ⟨hfall h, _, hJ', hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W64
        (.sub (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea) s :=
    (Spec.sub_reg_reg asz₁ rd rs).le_wp s (Program.wp_cons hN h₂)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN) h₁

@[ascend default + 1] theorem wrp_subJcc {r₀ : BitVec 64} {ra₀ : Int64} (asz₁ asz₂ osz : Width) (rd rs : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s =>
      let s' := { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status := StatusFlags.ofSub (s.regs.get64 rd) (s.regs.get64 rs) }
      (cc.cmp (s.regs.get64 rd) (s.regs.get64 rs) = true → (AddrRel r₀ ra₀) (label l) (label l) s')
        ∧ (cc.cmp (s.regs.get64 rd) (s.regs.get64 rs) = false → wrp (ofStateRepr abs) p (k ()) Q (AddrRel r₀ ra₀) s'))
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz₁ .W64
              (.sub (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (peek (fun st => cc.cmp (st.regs.get64 rd) (st.regs.get64 rs)) >>= fun c =>
            modifyIf (fun _ => True) (setReg64 rd fun st => st.regs.get64 rd - st.regs.get64 rs) >>= fun _ =>
            branch (stayIn (r₀)) (fun _ => c) (label l) >>= k) Q (AddrRel r₀ ra₀) := by
  rw [ofStateRepr_abs_eq]
  exact wrp_subJcc_rel asz₁ asz₂ osz rd rs cc l p k hN

/-- `cmp ra, rb; jcc c₁, l₁; jcc c₂, l₂` branches twice on one comparison: the flags survive the
first jump when it is not taken. -/
@[ascend default + 2] theorem wrp_cmpJccJcc_rel {M : DataMem → DataMem → Prop} {r₀ : BitVec 64} {ra₀ : Int64} (asz₁ asz₂ asz₃ osz₂ osz₃ : Width) (ra rb : Reg64)
    (c₁ c₂ : CondCode) (l₁ l₂ : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN₂ : Program.labels (Directive.instr (.regular asz₂ osz₂ (.jcc c₁ l₁))
      :: Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p) = [])
    (hN₃ : Program.labels (Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p) = []) :
    (fun s =>
      let s' := { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) }
      (c₁.cmp (s.regs.get64 ra) (s.regs.get64 rb) = true → (AddrRel r₀ ra₀) (label l₁) (label l₁) s')
        ∧ (c₁.cmp (s.regs.get64 ra) (s.regs.get64 rb) = false →
          (c₂.cmp (s.regs.get64 ra) (s.regs.get64 rb) = true → (AddrRel r₀ ra₀) (label l₂) (label l₂) s')
            ∧ (c₂.cmp (s.regs.get64 ra) (s.regs.get64 rb) = false →
              wrp (ofStateRel (JRel M)) p (k ()) Q (AddrRel r₀ ra₀) s')))
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz₁ .W64
              (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))
            :: Directive.instr (.regular asz₂ osz₂ (.jcc c₁ l₁))
            :: Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p)
          (branch (stayIn (r₀)) (fun st => c₁.cmp (st.regs.get64 ra) (st.regs.get64 rb)) (label l₁) >>= fun _ =>
            branch (stayIn (r₀)) (fun st => c₂.cmp (st.regs.get64 ra) (st.regs.get64 rb)) (label l₂) >>= k) Q (AddrRel r₀ ra₀) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, WPMonadExact.wp_bind_eq,
    wp_branch] at hs
  obtain ⟨⟨hjmp₁, hfall₁⟩, a, hJ, hw⟩ := hs
  rw [JRel.regs hJ] at hw
  let s' := { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) }
  have hpost : ∀ (l : Label) (cl : Int64), (AddrRel r₀ ra₀) (label l) cl s' → Ea.1 cl a →
      (ofStateRel (JRel M)).post (AddrRel r₀ ra₀) Ea.1 (label l) s' := by
    intro l cl he hea
    simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
      meet_prop_eq_and, ofStateRel_pred]
    exact ⟨cl, he, a, hJ, hea⟩
  have h₃ : wp (Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)))
      (fun _ => wp p ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea) s' →
      wp (Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p) ((ofStateRel (JRel M)).post Q Qa)
        (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea) s' := Program.wp_cons hN₃
  have h₂ : wp (Directive.instr (.regular asz₂ osz₂ (.jcc c₁ l₁)))
      (fun _ => wp (Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea) s' := by
    refine (Program.WP.Spec.jcc_label asz₂ osz₂ c₁ l₁).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_ofSub] at h
      simp only [h, ↓reduceIte] at hw
      exact hpost l₁ _ (hjmp₁ h) hw.2
    · rw [CondCode.interp_ofSub] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      obtain ⟨hjmp₂, hfall₂⟩ := hfall₁ h
      refine h₃ ((Program.WP.Spec.jcc_label asz₃ osz₃ c₂ l₂).le_wp _ ⟨fun h' => ?_, fun h' => ?_⟩)
      · rw [CondCode.interp_ofSub] at h'
        simp only [h', ↓reduceIte] at hw
        exact hpost l₂ _ (hjmp₂ h') hw.2
      · rw [CondCode.interp_ofSub] at h'
        simp only [h', Bool.false_eq_true, ↓reduceIte] at hw
        refine wrp_transport (P := wrp (ofStateRel (JRel M)) p (k ()) Q (AddrRel r₀ ra₀)) PartialOrder.rel_refl Qa Ea _ ?_
        simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
        exact ⟨hfall₂ h', a, hJ, hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W64
        (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz₂ (.jcc c₁ l₁))
          :: Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea) s :=
    (Program.WP.Spec.cmp_reg_reg asz₁ ra rb).le_wp s (Program.wp_cons hN₂ h₂)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN₂) h₁

@[ascend default + 2] theorem wrp_cmpJccJcc {r₀ : BitVec 64} {ra₀ : Int64} (asz₁ asz₂ asz₃ osz₂ osz₃ : Width) (ra rb : Reg64)
    (c₁ c₂ : CondCode) (l₁ l₂ : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN₂ : Program.labels (Directive.instr (.regular asz₂ osz₂ (.jcc c₁ l₁))
      :: Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p) = [])
    (hN₃ : Program.labels (Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p) = []) :
    (fun s =>
      let s' := { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) }
      (c₁.cmp (s.regs.get64 ra) (s.regs.get64 rb) = true → (AddrRel r₀ ra₀) (label l₁) (label l₁) s')
        ∧ (c₁.cmp (s.regs.get64 ra) (s.regs.get64 rb) = false →
          (c₂.cmp (s.regs.get64 ra) (s.regs.get64 rb) = true → (AddrRel r₀ ra₀) (label l₂) (label l₂) s')
            ∧ (c₂.cmp (s.regs.get64 ra) (s.regs.get64 rb) = false →
              wrp (ofStateRepr abs) p (k ()) Q (AddrRel r₀ ra₀) s')))
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz₁ .W64
              (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))
            :: Directive.instr (.regular asz₂ osz₂ (.jcc c₁ l₁))
            :: Directive.instr (.regular asz₃ osz₃ (.jcc c₂ l₂)) :: p)
          (branch (stayIn (r₀)) (fun st => c₁.cmp (st.regs.get64 ra) (st.regs.get64 rb)) (label l₁) >>= fun _ =>
            branch (stayIn (r₀)) (fun st => c₂.cmp (st.regs.get64 ra) (st.regs.get64 rb)) (label l₂) >>= k) Q (AddrRel r₀ ra₀) := by
  rw [ofStateRepr_abs_eq]
  exact wrp_cmpJccJcc_rel asz₁ asz₂ asz₃ osz₂ osz₃ ra rb c₁ c₂ l₁ l₂ p k hN₂ hN₃

/-- `test ra8, rb8; jcc cc, l` branches on the flags of the byte `ra8 &&& rb8`. -/
@[ascend default + 1] theorem wrp_testJcc8_rel {M : DataMem → DataMem → Prop} {r₀ : BitVec 64} {ra₀ : Int64} (asz₁ asz₂ osz : Width) (ra rb : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s => ∀ af : Bool,
      let v := (s.regs.get64 ra).take 8 &&& (s.regs.get64 rb).take 8
      let s' := { s with status := StatusFlags.from_result v { cf := false, af := af, of := false } }
      (cc.interp (StatusFlags.from_result v { cf := false, af := false, of := false }) = true →
          (AddrRel r₀ ra₀) (label l) (label l) s')
        ∧ (cc.interp (StatusFlags.from_result v { cf := false, af := false, of := false }) = false →
          wrp (ofStateRel (JRel M)) p (k ()) Q (AddrRel r₀ ra₀) s'))
      ⊑ wrp (ofStateRel (JRel M))
          (Directive.instr (.regular asz₁ .W8
              (.test (.reg (.low ra .W8)) (.regOrMem (.reg (.low rb .W8)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (branch (stayIn (r₀)) (fun st => cc.interp (StatusFlags.from_result
              ((st.regs.get64 ra).take 8 &&& (st.regs.get64 rb).take 8)
              { cf := false, af := false, of := false })) (label l) >>= k) Q (AddrRel r₀ ra₀) := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred, WPMonadExact.wp_bind_eq,
    wp_branch] at hs
  obtain ⟨hpre, a, hJ, hw⟩ := hs
  rw [JRel.regs hJ] at hw
  have h₂ : ∀ af : Bool, wp (Directive.instr (.regular asz₂ osz (.jcc cc l)))
      (fun _ => wp p ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea)
      { s with status := StatusFlags.from_result ((s.regs.get64 ra).take 8 &&& (s.regs.get64 rb).take 8) { cf := false, af := af, of := false } } := by
    intro af
    obtain ⟨hjmp, hfall⟩ := hpre af
    refine (Program.WP.Spec.jcc_label asz₂ osz cc l).le_wp _ ⟨fun h => ?_, fun h => ?_⟩
    · rw [CondCode.interp_from_result_af] at h
      simp only [h, ↓reduceIte] at hw
      show (ofStateRel (JRel M)).post (AddrRel r₀ ra₀) Ea.1 (label l) _
      simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply,
        meet_prop_eq_and, ofStateRel_pred]
      exact ⟨label l, hjmp h, a, hJ, hw.2⟩
    · rw [CondCode.interp_from_result_af] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hw
      refine wrp_transport (P := wrp (ofStateRel (JRel M)) p (k ()) Q (AddrRel r₀ ra₀)) PartialOrder.rel_refl Qa Ea _ ?_
      simp only [meet_apply, meet_prop_eq_and, ofStateRel_pred]
      exact ⟨hfall h, a, hJ, hw⟩
  have h₁ : wp (Directive.instr (.regular asz₁ .W8
        (.test (.reg (.low ra .W8)) (.regOrMem (.reg (.low rb .W8))))))
      (fun _ => wp (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
        ((ofStateRel (JRel M)).post Q Qa) (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea))
      (EPostsConcretization.ePosts (ofStateRel (JRel M)) (AddrRel r₀ ra₀) Ea) s :=
    (Spec.test_reg8_reg8 asz₁ ra rb).le_wp s fun af => Program.wp_cons hN (h₂ af)
  exact Program.wp_cons (by rw [Program.labels_cons_instr]; exact hN) h₁

@[ascend default + 1] theorem wrp_testJcc8 {r₀ : BitVec 64} {ra₀ : Int64} (asz₁ asz₂ osz : Width) (ra rb : Reg64) (cc : CondCode)
    (l : Label) (p : Program) (k : Unit → BlockM MachineData Unit)
    (hN : Program.labels (Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p) = []) :
    (fun s => ∀ af : Bool,
      let v := (s.regs.get64 ra).take 8 &&& (s.regs.get64 rb).take 8
      let s' := { s with status := StatusFlags.from_result v { cf := false, af := af, of := false } }
      (cc.interp (StatusFlags.from_result v { cf := false, af := false, of := false }) = true →
          (AddrRel r₀ ra₀) (label l) (label l) s')
        ∧ (cc.interp (StatusFlags.from_result v { cf := false, af := false, of := false }) = false →
          wrp (ofStateRepr abs) p (k ()) Q (AddrRel r₀ ra₀) s'))
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz₁ .W8
              (.test (.reg (.low ra .W8)) (.regOrMem (.reg (.low rb .W8)))))
            :: Directive.instr (.regular asz₂ osz (.jcc cc l)) :: p)
          (branch (stayIn (r₀)) (fun st => cc.interp (StatusFlags.from_result
              ((st.regs.get64 ra).take 8 &&& (st.regs.get64 rb).take 8)
              { cf := false, af := false, of := false })) (label l) >>= k) Q (AddrRel r₀ ra₀) := by
  rw [ofStateRepr_abs_eq]
  exact wrp_testJcc8_rel asz₁ asz₂ osz ra rb cc l p k hN

end
end Ascent.Kraken.AInstr

/-! ## Loads and stores through a base register

`mov r64, [b + d]` and `mov [b + d], r64` address memory through one base register and a
displacement, with no index. -/

namespace Ascent.Kraken.AInstr

section
variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
open scoped Program.WP

theorem Spec.mov_reg_mem (r b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true
        ∧ Q () { s with regs := s.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg, Reg64s.set_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, ite_true]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

end

section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}
  {E : Int64 → Int64 → MachineData → Prop}
open scoped Program.WP

@[ascend] theorem wrp_movRegMem (r b : Reg64) (d : Int64) :
    (fun s =>
      let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 8).isSome = true →
        Q () () { s with regs := s.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64
            (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
          (modifyIf (loadOk 8 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
            (loadReg 8 r (fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt) fun w _ => w)) Q E :=
  by
  refine wrp_modifyIf (g := loadOk 8 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
    (fun Q E s hp hq => (Spec.mov_reg_mem (Q := Q) (E := E) r b d).le_wp s ⟨hp, hq⟩) ?_
  intro s hg
  exact ⟨hg, by rw [loadReg, word_eight]; rfl⟩

@[ascend] theorem wrp_movMemReg (b : Reg64) (d : Int64) (rs : Reg64) :
    (fun s =>
      let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 8).isSome = true →
        Q () () { s with dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64
            (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low rs .W64))))))
          (modifyIf (storeOk 8 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
            (storeWord 8 (fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt) fun st => st.regs.get64 rs))
          Q E :=
  by
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf
    (g := storeOk 8 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
    (fun Q E s hp hq => (Program.WP.Spec.mov_mem_reg (Q := Q) (E := E) b d rs).le_wp s ⟨hp, hq⟩)
    fun s hg => ⟨hg, rfl⟩)
  intro s h hg
  exact h hg

@[ascend] theorem wrp_pushReg (rs : Reg64) :
    (fun s =>
      let a := s.regs.get64 .rsp - 8#64
      (Mem.loadInt s.dmem a 8).isSome = true →
        Q () () { s with regs := s.regs.set64 .rsp a, dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low rs .W64))))))
          (do
            modifyIf (storeOk 8 fun st => st.regs.get64 .rsp - 8#64)
              (storeWord 8 (fun st => st.regs.get64 .rsp - 8#64) fun st => st.regs.get64 rs)
            modifyIf (fun _ => True) (setReg64 .rsp fun st => st.regs.get64 .rsp - 8#64)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq, wp_modifyIf] at hs
  obtain ⟨hk, hm, -, hw⟩ := hs
  refine (Program.WP.Spec.push_reg rs).le_wp s ⟨hm, ?_⟩
  show (ofStateRepr abs).post Q Qa () _
  rw [Concretization.post_pi]
  exact ⟨(), hk hm, hw⟩

@[ascend] theorem wrp_popReg (rd : Reg64) :
    (fun s =>
      let v := BitVec.ofInt 64 (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).get!
      (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).isSome = true →
        Q () () { s with regs := (s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64)).set64 rd v })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular .W64 .W64 (.pop (.reg (.low rd .W64)))))
          (do
            modifyIf (fun _ => True) (setReg64 .rsp fun st => st.regs.get64 .rsp + 8#64)
            modifyIf (loadOk 8 fun st => st.regs.get64 .rsp - 8#64)
              (loadReg 8 rd (fun st => st.regs.get64 .rsp - 8#64) fun w _ => w)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq, wp_modifyIf,
    loadOk, setReg64_regs, setReg64_dmem, abs_regs, abs_dmem, Reg64s.get64_set64, ↓reduceIte,
    BitVec.add_sub_cancel] at hs
  obtain ⟨hk, -, hm, hw⟩ := hs
  refine (Program.WP.Spec.pop_reg rd).le_wp s ⟨hm, ?_⟩
  show (ofStateRepr abs).post Q Qa () _
  rw [Concretization.post_pi]
  refine ⟨(), hk hm, ?_⟩
  simp only [ofStateRepr_pred, loadReg, setReg64, word_eight, Reg64s.get64_set64, ↓reduceIte,
    BitVec.add_sub_cancel, abs_regs, abs_dmem] at hw ⊢
  exact hw

end
end Ascent.Kraken.AInstr

/-! ## Stack frames and narrow accesses

`sub rsp, k` and `add rsp, k` move the stack pointer by an immediate. A byte or 16-bit `mov` through a
base register and a displacement writes the low `n` bytes of a register or of memory: `movb al, 3(rsp)`
is `storeWord 1 (fun st => st.regs.get64 .rsp + 3) fun st => st.regs.get64 .rax`. A 16-bit `push`
or `pop` moves the stack pointer by two. -/

namespace Ascent.Kraken.AInstr

section
variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
open scoped Program.WP

theorem Spec.movzx_reg32_mem1 (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true ∧ Q () { s with regs := s.regs.set64 r (word 1 a s) } ⦄
      (Directive.instr (.regular .W64 .W32
          (@Operation.movzx .W32 .W8 (.reg (.low r .W32)) (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W32, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hv, Effects.All]
  refine hn _ ?_
  have hw : word 1 (s.regs.get64 b + BitVec.ofInt 64 d.toInt) s
      = BitVec.zeroExtend 64 (BitVec.zeroExtend Width.W32.bits (BitVec.ofInt Width.W8.bits v)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [word, hv, Option.get!_some, BitVec.toNat_setWidth, BitVec.toNat_ofInt, Width.bits,
      Int.natCast_pow]
    omega
  rw [← hw]
  exact hq

theorem Spec.push_reg16 (rs : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp - 2#64) 2).isSome = true
        ∧ Q () { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 2#64),
                        dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 2#64) 2 (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W16 (.push (.regOrMem (.reg (.low rs .W16))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.store, Reg64s.get_low_W16, Width.bytes, Width.bytesv, hv, Effects.All]
  rw [Mem.storeInt_take _ _ 2 16 (by omega) rfl]
  exact hn _ hq

theorem Spec.pop_reg16 (rd : Reg64) :
    ⦃ fun s =>
        let rs := s.regs.set64 .rsp (s.regs.get64 .rsp + 2#64)
        let v := BitVec.ofInt 16 (Mem.loadInt s.dmem (s.regs.get64 .rsp) 2).get!
        (Mem.loadInt s.dmem (s.regs.get64 .rsp) 2).isSome = true
          ∧ Q () { s with regs := rs.set64 rd ((rs.get64 rd).replaceLow v) } ⦄
      (Directive.instr (.regular .W64 .W16 (.pop (.reg (.low rd .W16)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load, MachineData.set,
    MachineData.setReg, Reg64s.set_low_W16, Width.bytes, Width.bytesv, hv, Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

end

section
variable [Host] [FunDecls] {Q : Unit → Unit → MachineData → Prop}
  {E : Int64 → Int64 → MachineData → Prop}
open scoped Program.WP

@[ascend] theorem wrp_subRegImm (asz : Width) (r : Reg64) (i : Int64) :
    (fun s => True → Q () () { s with
        regs := s.regs.set64 r (s.regs.get64 r - BitVec.setWidth 64 i.toBitVec),
        status := StatusFlags.ofSub (s.regs.get64 r) (BitVec.setWidth 64 i.toBitVec) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i)))))
          (modifyIf (fun _ => True) (setReg64 r fun st => st.regs.get64 r - BitVec.setWidth 64 i.toBitVec))
          Q E := by
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.sub_reg_imm (Q := Q) (E := E) asz r i).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_addRegImm (asz : Width) (r : Reg64) (i : Int64) :
    (fun s => True → Q () () { s with
        regs := s.regs.set64 r (s.regs.get64 r + BitVec.setWidth 64 i.toBitVec),
        status := StatusFlags.ofAdd (BitVec.setWidth 64 i.toBitVec) (s.regs.get64 r) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i)))))
          (modifyIf (fun _ => True) (setReg64 r fun st => st.regs.get64 r + BitVec.setWidth 64 i.toBitVec))
          Q E := by
  simp only [BitVec.add_comm _ (BitVec.setWidth 64 i.toBitVec)]
  refine wrp_modifyIf (pre := fun _ => True) (g := fun _ => True)
    (fun Q E s _ hq => (Program.WP.Spec.add_reg_imm (Q := Q) (E := E) asz r i).le_wp s hq) ?_
  intro s _
  exact ⟨trivial, rfl⟩

@[ascend] theorem wrp_movMemReg8 (b : Reg64) (d : Int64) (rs : Reg64) :
    (fun s =>
      let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 1).isSome = true →
        Q () () { s with dmem := Mem.storeInt s.dmem a 1 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W8
            (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low rs .W8))))))
          (modifyIf (storeOk 1 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
            (storeWord 1 (fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt) fun st => st.regs.get64 rs))
          Q E := by
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf
    (g := storeOk 1 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
    (fun Q E s hp hq => (Program.WP.Spec.mov_mem_reg8 (Q := Q) (E := E) b d rs).le_wp s
      ⟨hp, by rwa [Reg64s.get_low_W8, Mem.storeInt_take _ _ 1 8 (by omega) rfl]⟩)
    fun s hg => ⟨hg, rfl⟩)
  intro s h hg
  exact h hg

@[ascend] theorem wrp_movMemReg16 (b : Reg64) (d : Int64) (rs : Reg64) :
    (fun s =>
      let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 2).isSome = true →
        Q () () { s with dmem := Mem.storeInt s.dmem a 2 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W16
            (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low rs .W16))))))
          (modifyIf (storeOk 2 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
            (storeWord 2 (fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt) fun st => st.regs.get64 rs))
          Q E := by
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf
    (g := storeOk 2 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
    (fun Q E s hp hq => (Program.WP.Spec.mov_mem_reg16 (Q := Q) (E := E) b d rs).le_wp s
      ⟨hp, by rwa [Reg64s.get_low_W16, Mem.storeInt_take _ _ 2 16 (by omega) rfl]⟩)
    fun s hg => ⟨hg, rfl⟩)
  intro s h hg
  exact h hg

@[ascend] theorem wrp_movReg8Mem (r b : Reg64) (d : Int64) :
    (fun s =>
      let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 1).isSome = true →
        let v := BitVec.ofInt 8 (Mem.loadInt s.dmem a 1).get!
        Q () () { s with regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W8
            (.mov (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
          (modifyIf (loadOk 1 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
            (loadReg 1 r (fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
              fun w st => (st.regs.get64 r).replaceLow (w.setWidth 8))) Q E := by
  refine wrp_modifyIf (g := loadOk 1 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
    (fun Q E s hp hq => (Program.WP.Spec.mov_reg8_mem (Q := Q) (E := E) r b d).le_wp s ⟨hp, hq⟩) ?_
  intro s hg
  exact ⟨hg, by rw [loadReg, word_setWidth 1 8 (by omega) rfl]; rfl⟩

@[ascend] theorem wrp_movReg16Mem (r b : Reg64) (d : Int64) :
    (fun s =>
      let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 2).isSome = true →
        let v := BitVec.ofInt 16 (Mem.loadInt s.dmem a 2).get!
        Q () () { s with regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W16
            (.mov (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
          (modifyIf (loadOk 2 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
            (loadReg 2 r (fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
              fun w st => (st.regs.get64 r).replaceLow (w.setWidth 16))) Q E := by
  refine wrp_modifyIf (g := loadOk 2 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
    (fun Q E s hp hq => (Program.WP.Spec.mov_reg16_mem (Q := Q) (E := E) r b d).le_wp s ⟨hp, hq⟩) ?_
  intro s hg
  exact ⟨hg, by rw [loadReg, word_setWidth 2 16 (by omega) rfl]; rfl⟩

@[ascend] theorem wrp_movzxRegMem1 (r b : Reg64) (d : Int64) :
    (fun s =>
      let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 1).isSome = true → Q () () { s with regs := s.regs.set64 r (word 1 a s) })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W32
            (@Operation.movzx .W32 .W8 (.reg (.low r .W32)) (.mem ⟨some (.reg b), none, .int64 d⟩))))
          (modifyIf (loadOk 1 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
            (loadReg 1 r (fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt) fun w _ => w)) Q E := by
  refine wrp_modifyIf (g := loadOk 1 fun st => st.regs.get64 b + BitVec.ofInt 64 d.toInt)
    (fun Q E s hp hq => (Spec.movzx_reg32_mem1 (Q := Q) (E := E) r b d).le_wp s ⟨hp, hq⟩) ?_
  intro s hg
  exact ⟨hg, rfl⟩

@[ascend] theorem wrp_pushReg16 (rs : Reg64) :
    (fun s =>
      let a := s.regs.get64 .rsp - 2#64
      (Mem.loadInt s.dmem a 2).isSome = true →
        Q () () { s with regs := s.regs.set64 .rsp a, dmem := Mem.storeInt s.dmem a 2 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular .W64 .W16 (.push (.regOrMem (.reg (.low rs .W16))))))
          (do
            modifyIf (storeOk 2 fun st => st.regs.get64 .rsp - 2#64)
              (storeWord 2 (fun st => st.regs.get64 .rsp - 2#64) fun st => st.regs.get64 rs)
            modifyIf (fun _ => True) (setReg64 .rsp fun st => st.regs.get64 .rsp - 2#64)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq, wp_modifyIf] at hs
  obtain ⟨hk, hm, -, hw⟩ := hs
  refine (Spec.push_reg16 rs).le_wp s ⟨hm, ?_⟩
  show (ofStateRepr abs).post Q Qa () _
  rw [Concretization.post_pi]
  exact ⟨(), hk hm, hw⟩

@[ascend] theorem wrp_popReg16 (rd : Reg64) :
    (fun s =>
      let v := BitVec.ofInt 16 (Mem.loadInt s.dmem (s.regs.get64 .rsp) 2).get!
      let rs := s.regs.set64 .rsp (s.regs.get64 .rsp + 2#64)
      (Mem.loadInt s.dmem (s.regs.get64 .rsp) 2).isSome = true →
        Q () () { s with regs := rs.set64 rd ((rs.get64 rd).replaceLow v) })
      ⊑ wrp (ofStateRepr abs) (Directive.instr (.regular .W64 .W16 (.pop (.reg (.low rd .W16)))))
          (do
            modifyIf (fun _ => True) (setReg64 .rsp fun st => st.regs.get64 .rsp + 2#64)
            modifyIf (loadOk 2 fun st => st.regs.get64 .rsp - 2#64)
              (loadReg 2 rd (fun st => st.regs.get64 .rsp - 2#64)
                fun w st => (st.regs.get64 rd).replaceLow (w.setWidth 16))) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq, wp_modifyIf,
    loadOk, setReg64_regs, setReg64_dmem, abs_regs, abs_dmem, Reg64s.get64_set64, ↓reduceIte,
    BitVec.add_sub_cancel] at hs
  obtain ⟨hk, -, hm, hw⟩ := hs
  refine (Spec.pop_reg16 rd).le_wp s ⟨hm, ?_⟩
  show (ofStateRepr abs).post Q Qa () _
  rw [Concretization.post_pi]
  refine ⟨(), by simpa only [Reg64s.get64_set64] using hk hm, ?_⟩
  simp only [ofStateRepr_pred, loadReg, setReg64, word_setWidth 2 16 (by omega) rfl, Reg64s.get64_set64,
    ↓reduceIte, BitVec.add_sub_cancel, abs_regs, abs_dmem] at hw ⊢
  exact hw

end
end Ascent.Kraken.AInstr
