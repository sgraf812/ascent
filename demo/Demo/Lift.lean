import Demo.ZipStruct

/-!
# Register lifting

A program over `MachineData` refines a program over the data memory alone, under
`ofStateRepr MachineData.dmem`. A register read in the concrete program becomes a value of the
abstract program: the hypothesis `PureRefinement (t.regs.get64 r) x True Eq` relates the register
`r` of the state `t` to the abstract value `x`, and the `@[ascend_pure]` rules below abstract a
value computed from registers to the same computation on the abstract values. A step that writes a
register binds the abstract value of the written value to a variable of the abstract program.

The step rules know no instruction. They match the three writes of `Demo.L1`: a load into a
register `loadReg n` becomes `load n` and binds the loaded word, a store `storeWord n` becomes
`store n`, a register write `setReg64` leaves the memory unchanged and adds no abstract step, and an
exit `exitIf g f l` whose guard `g` reads a mapped word becomes `assume g'; throw l` with the guard
`g'` restated over the data memory.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Kraken

/-! ## Memory steps -/

/-- The `n`-byte word at `a`, zero-extended to 64 bits, undefined behaviour when the cell is not
mapped. -/
noncomputable def load (n : Nat) (a : BitVec 64) : BlockM DataMem (BitVec 64) := fun m =>
  Demonic.assume ((Mem.loadInt m a n).isSome = true) >>= fun _ =>
    pure (.ok (BitVec.ofInt 64 ((Mem.loadInt m a n).get! % 2 ^ (8 * n))), m)

/-- Store the low `n` bytes of `v` at `a`, undefined behaviour unless the cell is mapped. -/
noncomputable def store (n : Nat) (a v : BitVec 64) : BlockM DataMem Unit :=
  modifyIf (fun m => (Mem.loadInt m a n).isSome = true) fun m => Mem.storeInt m a n v.toInt

theorem ofInt_emod_two_pow (n : Nat) (x : Int) : BitVec.ofInt n (x % 2 ^ n) = BitVec.ofInt n x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, Int.natCast_pow, Int.cast_ofNat_Int, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]

section
variable (Q : BitVec 64 → DataMem → Prop) (Qu : Unit → DataMem → Prop)
  (E : (Int64 → DataMem → Prop) × EStack⟨⟩) (m : DataMem)

theorem wp_load (n : Nat) (a : BitVec 64) :
    wp (load n a) Q E m
      = ((Mem.loadInt m a n).isSome = true
          ∧ Q (BitVec.ofInt 64 ((Mem.loadInt m a n).get! % 2 ^ (8 * n))) m) := by
  rw [wp_BlockM_eq, show (load n a).run.run m = load n a m from rfl, load]
  by_cases h : (Mem.loadInt m a n).isSome = true
  · rw [Demonic.assume_bind_of_pos h]
    simp only [h, true_and]
    rfl
  · rw [Demonic.assume_bind_of_neg h]
    simp only [Bool.not_eq_true] at h
    simp [h]

theorem wp_store (n : Nat) (a v : BitVec 64) :
    wp (store n a v) Qu E m
      = ((Mem.loadInt m a n).isSome = true ∧ Qu () (Mem.storeInt m a n v.toInt)) :=
  wp_modifyIf _ _ _ _ _

theorem _root_.Mem.Mapped.loadInt_isSome_single {m : DataMem} {a : BitVec 64} {n : Nat}
    (h : Mem.Mapped [(a, n)] m) : (Mem.loadInt m a n).isSome = true :=
  Mem.Mapped.loadInt_isSome h (Mem.Blocks.Inside.base (Nat.le_refl _))

grind_pattern Mem.Mapped.loadInt_isSome_single => Mem.Mapped [(a, n)] m, Mem.loadInt m a n

@[spec] theorem Spec.load (n : Nat) (a : BitVec 64) :
    ⦃fun m => (Mem.loadInt m a n).isSome = true
      ∧ Q (BitVec.ofInt 64 ((Mem.loadInt m a n).get! % 2 ^ (8 * n))) m⦄ load n a ⦃Q; E⦄ :=
  ⟨fun m h => by rw [wp_load]; exact h⟩

@[spec] theorem Spec.store (n : Nat) (a v : BitVec 64) :
    ⦃fun m => (Mem.loadInt m a n).isSome = true ∧ Qu () (Mem.storeInt m a n v.toInt)⦄
      store n a v ⦃Qu; E⦄ :=
  ⟨fun m h => by rw [wp_store]; exact h⟩

theorem wp_assume_throw {α : Type} {Qα : α → DataMem → Prop} (g : DataMem → Prop) (l : Int64) :
    wp (do StateT.assume g; throw l : BlockM DataMem α) Qα E m = (g m ∧ E.1 l m) := by
  rw [WPMonadExact.wp_bind_eq, ExceptT.wp_monadLift_StateT_Demonic, StateT.wp_assume_eq, wp_throw_block]

end

/-- `c ≐ x`: the concrete value `c` abstracts to the abstract value `x`. -/
scoped notation:50 c:51 " ≐ " x:51 => PureRefinement c x True Eq

theorem setWidth_ofInt {b : Nat} (hb : b ≤ 64) (x : Int) :
    (BitVec.ofInt b x).setWidth 64 = BitVec.ofInt 64 (x % 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  have hposN : 0 < 2 ^ b := Nat.two_pow_pos b
  have hleN : 2 ^ b ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hb
  have hpos : (0 : Int) < 2 ^ b := by exact_mod_cast hposN
  have hle : (2 : Int) ^ b ≤ 2 ^ 64 := by exact_mod_cast hleN
  have h0 : 0 ≤ x % 2 ^ b := Int.emod_nonneg _ (by omega)
  have hlt : x % 2 ^ b < 2 ^ b := Int.emod_lt_of_pos _ hpos
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt h0 (by omega)]
  have : (x % 2 ^ b).toNat < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt this

/-! ## Offsets -/

theorem add_ofInt_neg (x : BitVec 64) (d : Int64) :
    x + BitVec.ofInt 64 (-d).toInt = x - BitVec.ofInt 64 d.toInt := by
  rw [BitVec.ofInt_int64ToInt, BitVec.ofInt_int64ToInt, Int64.toBitVec_neg, BitVec.add_neg_eq_sub]

/-! ## Values -/

/-- `RegsRel rs t`: each register `r` of `rs` holds its abstract value `v` in the state `t`. -/
abbrev RegsRel : List (Reg64 × BitVec 64) → MachineData → Prop
  | [], _ => True
  | (r, v) :: rs, t => t.regs.get64 r ≐ v ∧ RegsRel rs t

attribute [vcgen_simp] RegsRel

section
variable {w : Nat} {a b x y : BitVec w} {P₁ P₂ : Prop}

@[ascend_pure] theorem abs_add (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_sub (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a - b) (x - y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_beq (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a == b) (x == y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_mul (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a * b) (x * y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_and (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a &&& b) (x &&& y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_ushiftRight (k : Nat) (h₁ : PureRefinement a x P₁ Eq) :
    PureRefinement (a.ushiftRight k) (x.ushiftRight k) P₁ Eq := fun hp₁ => by
  rw [h₁ hp₁]

@[ascend_pure] theorem abs_cmp {cc : CondCode} {a b x y : BitVec 64}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (cc.cmp a b) (cc.cmp x y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_sib {t : MachineData} {k : Nat} {b i : Reg64} {d : Int64} {x y : BitVec 64}
    (hb : PureRefinement (t.regs.get64 b) x P₁ Eq) (hi : PureRefinement (t.regs.get64 i) y P₂ Eq) :
    PureRefinement (sib k b i d t) (x + y * BitVec.ofNat 64 k + BitVec.ofInt 64 d.toInt) (P₁ ∧ P₂) Eq :=
  fun ⟨hp₁, hp₂⟩ => by rw [sib, hb hp₁, hi hp₂]

@[ascend_pure] theorem abs_not {c d : Bool} (h : PureRefinement c d P₁ Eq) :
    PureRefinement (!c) (!d) P₁ Eq := fun hp => by
  rw [h hp]

@[ascend_pure] theorem abs_eqProp {α : Type} {a b x y : α}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a = b) (x = y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_notProp {p q : Prop} (h : PureRefinement p q P₁ Eq) :
    PureRefinement (¬p) (¬q) P₁ Eq := fun hp => by
  rw [h hp]

@[ascend_pure] theorem abs_pair {α β : Type} {a x : α} {b y : β}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a, b) (x, y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_fst {α β : Type} {p q : α × β} (h : PureRefinement p q P₁ Eq) :
    PureRefinement p.1 q.1 P₁ Eq := fun hp => by rw [h hp]

@[ascend_pure] theorem abs_snd {α β : Type} {p q : α × β} (h : PureRefinement p q P₁ Eq) :
    PureRefinement p.2 q.2 P₁ Eq := fun hp => by rw [h hp]

@[ascend_pure low] theorem abs_refl {α : Type} {c : α} : PureRefinement c c True Eq :=
  PureRefinement.of_rel rfl

end

/-! ## Words as numbers

`WordNat x n` states that the word `x` holds the number `n`. Under `x ≐ₙ n`, an addition of words
abstracts to the addition of the numbers, and a comparison of words abstracts to the comparison of
the numbers with the range of the numbers as its precondition. -/

def WordNat {w : Nat} (x : BitVec w) (n : Nat) : Prop := x = BitVec.ofNat w n

scoped notation:50 c:51 " ≐ₙ " x:51 => PureRefinement c x True WordNat

theorem beq_eq_true_eq {α : Type} [BEq α] [LawfulBEq α] (a b : α) : ((a == b) = true) = (a = b) :=
  propext beq_iff_eq

theorem bne_eq_true_eq {α : Type} [BEq α] [LawfulBEq α] (a b : α) : ((a != b) = true) = ¬a = b :=
  propext bne_iff_ne

section
variable {w : Nat} {x y : BitVec w} {i j : Nat} {P₁ P₂ : Prop}

@[ascend_pure] theorem absN_ofNat {n : Nat} : PureRefinement (BitVec.ofNat w n) n True WordNat :=
  PureRefinement.of_rel rfl

@[ascend_pure] theorem absN_add (h₁ : PureRefinement x i P₁ WordNat) (h₂ : PureRefinement y j P₂ WordNat) :
    PureRefinement (x + y) (i + j) (P₁ ∧ P₂) WordNat := fun ⟨hp₁, hp₂⟩ => by
  rw [WordNat, h₁ hp₁, h₂ hp₂, BitVec.ofNat_add]

theorem ofNat_eq_ofNat_iff {n m : Nat} (hn : n < 2 ^ w) (hm : m < 2 ^ w) :
    BitVec.ofNat w n = BitVec.ofNat w m ↔ n = m := by
  rw [BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hm]

@[ascend_pure] theorem absN_sub (h₁ : PureRefinement x i P₁ WordNat) (h₂ : PureRefinement y j P₂ WordNat) :
    PureRefinement (x - y) (i - j) (P₁ ∧ P₂ ∧ j ≤ i ∧ i < 2 ^ w) WordNat :=
  fun ⟨hp₁, hp₂, hji, hi⟩ => by
    rw [WordNat, h₁ hp₁, h₂ hp₂]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega : j < 2 ^ w), Nat.mod_eq_of_lt (by omega : i - j < 2 ^ w),
      show 2 ^ w - j + i = (i - j) + 2 ^ w by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

@[ascend_pure high] theorem absN_beq (h₁ : PureRefinement x i P₁ WordNat)
    (h₂ : PureRefinement y j P₂ WordNat) :
    PureRefinement (x == y) (i == j) (P₁ ∧ P₂ ∧ i < 2 ^ w ∧ j < 2 ^ w) Eq :=
  fun ⟨hp₁, hp₂, hi, hj⟩ => by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁ hp₁, h₂ hp₂, ofNat_eq_ofNat_iff hi hj]

end

section
variable {a b : BitVec 64} {n m : Nat} {P₁ P₂ : Prop}

@[ascend_pure high] theorem absN_cmp_nz (h₁ : PureRefinement a n P₁ WordNat)
    (h₂ : PureRefinement b m P₂ WordNat) :
    PureRefinement (CondCode.nz.cmp a b) (n != m) (P₁ ∧ P₂ ∧ n < 2 ^ 64 ∧ m < 2 ^ 64) Eq :=
  fun ⟨hp₁, hp₂, hn, hm⟩ => by
    rw [Bool.eq_iff_iff, CondCode.cmp_nz_eq_true, h₁ hp₁, h₂ hp₂, bne_iff_ne, ne_eq, ne_eq,
      ofNat_eq_ofNat_iff hn hm]

@[ascend_pure high] theorem absN_cmp_z_self_zero (h : PureRefinement a n P₁ WordNat) :
    PureRefinement (CondCode.z.cmp (a &&& a) 0#64) (n == 0) (P₁ ∧ n < 2 ^ 64) Eq :=
  fun ⟨hp, hn⟩ => by
    rw [Bool.eq_iff_iff, CondCode.cmp_z_eq_true, BitVec.and_self, h hp, beq_iff_eq]
    exact ofNat_eq_ofNat_iff hn (by omega)

theorem WordNat.sub_one_beq_zero {x : BitVec 64} {i : Nat} (h : WordNat x i) (hi : 0 < i)
    (hb : i < 2 ^ 64) : (x - 1#64 == 0#64) = (i == 1) := by
  rw [WordNat] at h
  subst h
  have key : (BitVec.ofNat 64 i - 1#64 = 0#64) ↔ i = 1 := by
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at this
      omega
    · rintro rfl; rfl
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact key

grind_pattern WordNat.sub_one_beq_zero => WordNat x i, x - 1#64 == 0#64

@[ascend_pure high] theorem absN_cmp_be (h₁ : PureRefinement a n P₁ WordNat)
    (h₂ : PureRefinement b m P₂ WordNat) :
    PureRefinement (CondCode.be.cmp a b) (Nat.ble n m) (P₁ ∧ P₂ ∧ n < 2 ^ 64 ∧ m < 2 ^ 64) Eq :=
  fun ⟨hp₁, hp₂, hn, hm⟩ => by
    rw [Bool.eq_iff_iff, CondCode.cmp_be_eq_true, h₁ hp₁, h₂ hp₂, Nat.ble_eq, BitVec.le_def,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm]

theorem WordNat.cmp_be_eq {x y : BitVec 64} {i j : Nat} (hx : WordNat x i) (hy : WordNat y j)
    (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) : (CondCode.be.cmp x y = true) = (i ≤ j) := by
  rw [absN_cmp_be (PureRefinement.of_rel hx) (PureRefinement.of_rel hy) ⟨trivial, trivial, hi, hj⟩,
    Nat.ble_eq]

grind_pattern WordNat.cmp_be_eq => WordNat x i, WordNat y j, CondCode.be.cmp x y

@[ascend_pure high] theorem absEq_ofWordNat {x : BitVec 64} {n : Nat} (h : PureRefinement x n P₁ WordNat) :
    PureRefinement x (BitVec.ofNat 64 n) P₁ Eq := h

def encodeIdx : Option Nat → BitVec 64
  | none => 18446744073709551615#64
  | some j => BitVec.ofNat 64 j

def IdxWord (v : BitVec 64) (o : Option Nat) : Prop := v = encodeIdx o

@[grind =] theorem encodeIdx_none : encodeIdx none = 18446744073709551615#64 := rfl
@[grind =] theorem encodeIdx_some (j : Nat) : encodeIdx (some j) = BitVec.ofNat 64 j := rfl

def Unrelated (_ : α) (_ : β) : Prop := True

@[ascend_pure low] theorem abs_unrelated (c : α) (a : β) : PureRefinement c a True Unrelated :=
  fun _ => trivial

@[ascend_pure high] theorem absIdx_none : PureRefinement (18446744073709551615#64) none True IdxWord :=
  fun _ => rfl

@[ascend_pure] theorem absIdx_some (h : PureRefinement x j P₁ WordNat) :
    PureRefinement x (some j) P₁ IdxWord := h

@[ascend_pure] theorem absN_ushiftRight (k : Nat) (h : PureRefinement a n P₁ WordNat) :
    PureRefinement (a.ushiftRight k) (n / 2 ^ k) (P₁ ∧ n < 2 ^ 64) WordNat :=
  fun ⟨hp, hn⟩ => by
    rw [WordNat, h hp]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 64 n >>> k).toNat = _
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

@[ascend_pure high] theorem absN_cmp_le_self_zero (h : PureRefinement a n P₁ WordNat) :
    PureRefinement (CondCode.le.cmp (a &&& a) 0#64) (n == 0) (P₁ ∧ n < 2 ^ 63) Eq :=
  fun ⟨hp, hn⟩ => by
    rw [Bool.eq_iff_iff, CondCode.cmp_le_eq_true, BitVec.and_self, h hp, beq_iff_eq,
      BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, BitVec.toInt_zero]
    split <;> omega

end

/-! ## Steps -/

attribute [ascend] wrp_bind

section
variable {Q : Unit → BitVec 64 → MachineData → Prop} {Qu : Unit → Unit → MachineData → Prop}
  {E : (Int64 → Int64 → MachineData → Prop) × EStack⟨⟩}

@[ascend] theorem wrp_pure_unit :
    Qu () () ⊑ wrp (ofStateRepr MachineData.dmem) (pure () : BlockM MachineData Unit)
      (pure () : BlockM DataMem Unit) Qu E :=
  wrp_pure () ()

@[ascend] theorem wrp_loadReg_load (n : Nat) (r : Reg64) (a : MachineData → BitVec 64)
    (e : BitVec 64 → MachineData → BitVec 64) (pa : BitVec 64) :
    (fun t => a t ≐ pa ∧
      (loadOk n a t → ∀ w, word n (a t) t ≐ w → Q () w (loadReg n r a e t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (loadOk n a) (loadReg n r a e))
          (load n pa) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_load] at ht
  obtain ⟨⟨ha, hk⟩, hl, hq⟩ := ht
  have ha : a t = pa := ha trivial
  have hg : loadOk n a t := by rw [loadOk, ha]; exact hl
  rw [wp_modifyIf, Concretization.post_pi]
  refine ⟨hg, _, hk hg _ (PureRefinement.of_rel ?_), hq⟩
  rw [word, ha]

@[ascend] theorem wrp_storeWord_store (n : Nat) (a v : MachineData → BitVec 64) (pa pv : BitVec 64) :
    (fun t => a t ≐ pa ∧ v t ≐ pv ∧ (storeOk n a t → Qu () () (storeWord n a v t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (storeOk n a) (storeWord n a v))
          (store n pa pv) Qu E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_store] at ht
  obtain ⟨⟨ha, hv, hk⟩, hl, hq⟩ := ht
  have ha : a t = pa := ha trivial
  have hv : v t = pv := hv trivial
  have hg : storeOk n a t := by rw [storeOk, loadOk, ha]; exact hl
  rw [wp_modifyIf, Concretization.post_pi]
  refine ⟨hg, (), hk hg, ?_⟩
  simp only [ofStateRepr_pred, storeWord, ha, hv]
  exact hq

@[ascend] theorem wrp_peek_pure {γ : Type} {Qγ : γ → γ → MachineData → Prop} (c : MachineData → γ) (b : γ) :
    (fun t => c t ≐ b ∧ ∀ z, c t ≐ z → Qγ (c t) z t)
      ⊑ wrp (ofStateRepr MachineData.dmem) (peek c) (pure b : BlockM DataMem γ) Qγ E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at ht
  obtain ⟨⟨hb, hq⟩, hqa⟩ := ht
  rw [wp_peek, Concretization.post_pi]
  exact ⟨b, hq b hb, hqa⟩

end

/-! ## Control -/

section
variable {σa : Type} {view : DataMem → σa} {E : (Int64 → Int64 → DataMem → Prop) × EStack⟨⟩}

@[ascend default + 1] theorem wrp_assume_throw {CV AV : Type} {Q : CV → AV → DataMem → Prop}
    (g : DataMem → Prop) (l : Int64) :
    (fun m => g m ∧ E.1 l l m)
      ⊑ wrp (ofStateRepr view) (do StateT.assume g; throw l : BlockM DataMem CV)
          (throw l : BlockM σa AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_throw_block] at hm
  obtain ⟨⟨hg, he⟩, hw⟩ := hm
  rw [wp_assume_throw]
  refine ⟨hg, ?_⟩
  simp only [EPostsConcretization.ePosts_cons]
  rw [Concretization.post_pi]
  exact ⟨l, he, hw⟩

end

section
variable {σc σa : Type} {view : σc → σa} {E : (Int64 → Int64 → σc → Prop) × EStack⟨⟩}

theorem wrp_forIn_lockstep_bind_unit {βc βa : Type} (R : LockstepInvariant βc σc βa) (cinit : βc)
    (ainit : βa) {fc : Unit → βc → BlockM σc (ForInStep βc)}
    {fa : βa → BlockM σa (ForInStep βa)} {Q : Unit → Unit → σc → Prop}
    (hbody : ∀ c i, (fun t => R c t i) ⊑ wrp (ofStateRepr view) (fc () c) (fa i)
      (fun rc ra t => match rc with
        | .yield c' => ∃ a', R c' t a' ∧ ra = .yield a'
        | .done _ => ∃ a', Q () () t ∧ ra = .done a') E) :
    (fun t => R cinit t ainit) ⊑ wrp (ofStateRepr view)
      (FixLoop.mk.forIn cinit fc >>= fun _ => pure ())
      (FixLoop.mk.forIn ainit (fun _ v => fa v) >>= fun _ => pure ()) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq,
    WPMonadExact.wp_pure_eq] at ht
  have h := wrp_transport (wrp_forIn_lockstep R cinit ainit (fa := fa)
    (Q := fun _ _ t => Q () () t) fun c i => PartialOrder.rel_trans (hbody c i)
      (wrp_mono_post fun rc ra t h => by cases rc <;> exact h))
    (fun _ => Qa ()) Ea t
    (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ht)
  rw [WPMonadExact.wp_bind_eq]
  refine WP.wp_monotone_post (x := FixLoop.mk.forIn cinit fc) ?_ t h
  intro u t' h'
  rw [Concretization.post_pi] at h'
  obtain ⟨_, hq, hqa⟩ := h'
  simp only [WPMonadExact.wp_pure_eq]
  rw [Concretization.post_pi]
  exact ⟨(), hq, hqa⟩

@[ascend] theorem wrp_assume_skip {Q : PUnit → PUnit → σc → Prop} (g : σc → Prop) :
    (fun m => g m ∧ Q () () m)
      ⊑ wrp (ofStateRepr view) (do StateT.assume g : BlockM σc PUnit)
          (pure () : BlockM σa PUnit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at hm
  obtain ⟨⟨hg, hq⟩, hw⟩ := hm
  simp only [ExceptT.wp_monadLift_StateT_Demonic, StateT.wp_assume_eq]
  refine ⟨hg, ?_⟩
  rw [Concretization.post_pi]
  exact ⟨(), hq, hw⟩

@[ascend] theorem wrp_throw_throw {CV AV : Type} {Q : CV → AV → σc → Prop} (l : Int64) :
    (fun t => E.1 l l t)
      ⊑ wrp (ofStateRepr view) (throw l : BlockM σc CV) (throw l : BlockM σa AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_throw_block] at ht ⊢
  obtain ⟨he, hw⟩ := ht
  simp only [EPostsConcretization.ePosts_cons]
  rw [Concretization.post_pi]
  exact ⟨l, he, hw⟩

@[ascend] theorem wrp_pure_unit_post {γ : Type} {Q : PUnit → γ → σc → Prop} (c : PUnit) (b : γ) :
    (fun t => Q c b t) ⊑ wrp (ofStateRepr view) (pure c : BlockM σc PUnit) (pure b : BlockM σa γ) Q E :=
  wrp_pure (Q := Q) c b

@[ascend 50] theorem wrp_pure_post {γ δ : Type} {Q : γ → δ → σc → Prop} (c : γ) (b : δ) :
    (fun t => Q c b t) ⊑ wrp (ofStateRepr view) (pure c : BlockM σc γ) (pure b : BlockM σa δ) Q E :=
  wrp_pure (Q := Q) c b

@[ascend low] theorem wrp_pure_val {γ : Type} {Q : γ → γ → σc → Prop} (c b : γ) (P : Prop) :
    (fun t => PureRefinement c b P Eq ∧ P ∧ ∀ z, c ≐ z → Q c z t)
      ⊑ wrp (ofStateRepr view) (pure c : BlockM σc γ) (pure b : BlockM σa γ) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at ht ⊢
  obtain ⟨⟨hb, hP, hq⟩, hqa⟩ := ht
  rw [Concretization.post_pi]
  exact ⟨b, hq b (PureRefinement.of_rel (hb hP)), hqa⟩

end

section
variable {AV : Type} {Qu : Unit → AV → MachineData → Prop}
  {E : (Int64 → Int64 → MachineData → Prop) × EStack⟨⟩}

theorem wrp_forIn_lockstep_unit {βa : Type} (R : LockstepInvariant PUnit MachineData βa) (ab : βa)
    {fc : Unit → PUnit → BlockM MachineData (ForInStep PUnit)}
    {fa : βa → BlockM DataMem (ForInStep βa)}
    {Q : PUnit → Unit → MachineData → Prop}
    (hbody : ∀ v, (fun t => R () t v) ⊑ wrp (ofStateRepr MachineData.dmem) (fc () PUnit.unit) (fa v)
      (fun rc ra t => match rc with
        | .yield _ => ∃ a', R () t a' ∧ ra = .yield a'
        | .done u => ∃ a', Q u () t ∧ ra = .done a') E) :
    (fun t => R () t ab) ⊑ wrp (ofStateRepr MachineData.dmem) (FixLoop.mk.forIn PUnit.unit fc)
      (FixLoop.mk.forIn ab (fun _ v => fa v) >>= fun _ => pure ()) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq,
    WPMonadExact.wp_pure_eq] at ht
  have h := wrp_transport
    (wrp_forIn_lockstep R PUnit.unit ab (fa := fa)
      (Q := fun u _ t => Q u () t) fun _ v => PartialOrder.rel_trans (hbody v)
        (wrp_mono_post fun rc ra t h => by cases rc <;> exact h))
      (fun _ => Qa ()) Ea t
    (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ht)
  refine WP.wp_monotone_post (x := FixLoop.mk.forIn PUnit.unit fc) ?_ t h
  intro u t' h'
  rw [Concretization.post_pi] at h' ⊢
  obtain ⟨_, hq, hqa⟩ := h'
  exact ⟨(), hq, hqa⟩

@[ascend] theorem wrp_condState {σc σa CV AV : Type} {view : σc → σa}
    {E : (Int64 → Int64 → σc → Prop) × EStack⟨⟩} {Q : CV → AV → σc → Prop} {c : σc → Bool}
    {x y : BlockM σc CV} {ax ay : BlockM σa AV} (b : Bool) (P : Prop) :
    (fun t => PureRefinement (c t) b P Eq ∧ P ∧
      (b = true → wrp (ofStateRepr view) x ax Q E t) ∧
      (b = false → wrp (ofStateRepr view) y ay Q E t))
      ⊑ wrp (ofStateRepr view) (condState c x y) (condState (fun _ => b) ax ay) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_condState] at ht
  obtain ⟨⟨hb, hP, hx, hy⟩, hw⟩ := ht
  have hb : c t = b := hb hP
  rw [wp_condState]
  cases b with
  | true =>
    simp only [hb, ↓reduceIte] at hw ⊢
    exact wrp_transport (P := wrp (ofStateRepr view) x ax Q E) PartialOrder.rel_refl Qa Ea t
      (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ⟨hx rfl, hw⟩)
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    exact wrp_transport (P := wrp (ofStateRepr view) y ay Q E) PartialOrder.rel_refl Qa Ea t
      (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ⟨hy rfl, hw⟩)

@[ascend high] theorem wrp_stutter_bind {CV : Type} {Q : CV → AV → MachineData → Prop}
    (f : MachineData → MachineData)
    {k : Unit → BlockM MachineData CV} {a : BlockM DataMem AV} (hf : ∀ t, (f t).dmem = t.dmem) :
    (fun t => wrp (ofStateRepr MachineData.dmem) (k ()) a Q E (f t))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (fun _ => True) f >>= k) a Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at ht
  obtain ⟨hk, hw⟩ := ht
  rw [WPMonadExact.wp_bind_eq, wp_modifyIf]
  refine ⟨trivial, wrp_transport (P := wrp (ofStateRepr MachineData.dmem) (k ()) a Q E)
    PartialOrder.rel_refl Qa Ea (f t) ?_⟩
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, hf]
  exact ⟨hk, hw⟩

@[ascend] theorem wrp_exitIf_assume {CV AV : Type} {Q : CV → AV → MachineData → Prop}
    (a : MachineData → BitVec 64) (f : MachineData → MachineData) (l : Int64) (pa : BitVec 64)
    (hf : ∀ t, (f t).dmem = t.dmem) :
    (fun t => a t ≐ pa ∧ (loadOk 8 a t → E.1 l l (f t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (exitIf (loadOk 8 a) f l : BlockM MachineData CV)
          (do StateT.assume (fun m => (Mem.loadInt m pa 8).isSome = true); throw l : BlockM DataMem AV)
          Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_assume_throw] at ht
  obtain ⟨⟨ha, hk⟩, hl, he⟩ := ht
  have ha : a t = pa := ha trivial
  have hg : loadOk 8 a t := by rw [loadOk, ha]; exact hl
  rw [wp_exitIf]
  refine ⟨hg, ?_⟩
  simp only [EPostsConcretization.ePosts_cons]
  rw [Concretization.post_pi]
  refine ⟨l, hk hg, ?_⟩
  simp only [ofStateRepr_pred, hf]
  exact he

@[ascend] theorem wrp_exitIf_rsp {CV AV : Type} {Q : CV → AV → MachineData → Prop}
    (r₀ : BitVec 64) (f : MachineData → MachineData) (l : Int64) (pa : BitVec 64)
    (hf : ∀ t, (f t).dmem = t.dmem) :
    (fun t => t.regs.get64 .rsp ≐ pa ∧ (t.regs.rsp.toBitVec = r₀ → E.1 l l (f t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (exitIf (fun s => s.regs.rsp.toBitVec = r₀) f l : BlockM MachineData CV)
          (do StateT.assume (fun (_ : DataMem) => pa = r₀); throw l : BlockM DataMem AV)
          Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_assume_throw] at ht
  obtain ⟨⟨ha, hk⟩, hl, he⟩ := ht
  have hg : t.regs.rsp.toBitVec = r₀ := by rw [← Reg64s.get64_rsp]; exact (ha trivial).trans hl
  rw [wp_exitIf]
  refine ⟨hg, ?_⟩
  simp only [EPostsConcretization.ePosts_cons]
  rw [Concretization.post_pi]
  refine ⟨l, hk hg, ?_⟩
  simp only [ofStateRepr_pred, hf]
  exact he

/-- The return slot at `p` holds the address `ra`. -/
def retAddrAt (m : DataMem) (p : BitVec 64) : Option Int64 :=
  (Mem.loadInt m p 8).map fun i => Int64.ofBitVec (BitVec.ofInt 64 i)

@[grind =] theorem retAddrAt_eq (m : DataMem) (p : BitVec 64) :
    retAddrAt m p = (Mem.loadInt m p 8).map fun i => Int64.ofBitVec (BitVec.ofInt 64 i) := rfl

@[ascend] theorem wrp_exitIf_retOk {CV AV : Type} {Q : CV → AV → MachineData → Prop}
    (r₀ : BitVec 64) (ra : Int64) (f : MachineData → MachineData) (l : Int64) (pa : BitVec 64)
    (hf : ∀ t, (f t).dmem = t.dmem) :
    (fun t => t.regs.get64 .rsp ≐ pa ∧ (retOk r₀ ra t → E.1 l l (f t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (exitIf (retOk r₀ ra) f l : BlockM MachineData CV)
          (do StateT.assume (fun m => pa = r₀ ∧ retAddrAt m pa = some ra)
              throw l : BlockM DataMem AV)
          Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_assume_throw] at ht
  obtain ⟨⟨ha, hk⟩, ⟨hr, hl⟩, he⟩ := ht
  have ha : t.regs.get64 .rsp = pa := ha trivial
  have hg : retOk r₀ ra t := ⟨ha.trans hr, by rw [MachineData.retAddr_eq, ha]; exact hl⟩
  rw [wp_exitIf]
  refine ⟨hg, ?_⟩
  simp only [EPostsConcretization.ePosts_cons]
  rw [Concretization.post_pi]
  refine ⟨l, hk hg, ?_⟩
  simp only [ofStateRepr_pred, hf]
  exact he

theorem assume_true_bind {σ α : Type} (k : PUnit → BlockM σ α) :
    ((do StateT.assume (fun (_ : σ) => True) : BlockM σ PUnit) >>= k) = k PUnit.unit := by
  apply BlockLoop.ext_wp <;> intro Q E m <;>
    simp only [WPMonadExact.wp_bind_eq, ExceptT.wp_monadLift_StateT_Demonic, StateT.wp_assume_eq, true_and] <;>
    exact id

theorem assume_true {σ : Type} :
    (do StateT.assume (fun (_ : σ) => True) : BlockM σ PUnit) = pure PUnit.unit := by
  apply BlockLoop.ext_wp <;> intro Q E m <;>
    simp only [WPMonadExact.wp_pure_eq, ExceptT.wp_monadLift_StateT_Demonic, StateT.wp_assume_eq, true_and] <;>
    exact id

@[ascend] theorem wrp_modifyIf_retOk {Q : Unit → PUnit → MachineData → Prop}
    (r₀ : BitVec 64) (ra : Int64) (f : MachineData → MachineData) (pa : BitVec 64)
    (hf : ∀ t, (f t).dmem = t.dmem) :
    (fun t => t.regs.get64 .rsp ≐ pa ∧ (retOk r₀ ra t → Q () () (f t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (retOk r₀ ra) f : BlockM MachineData Unit)
          (do StateT.assume (fun m => pa = r₀ ∧ retAddrAt m pa = some ra)
            : BlockM DataMem PUnit)
          Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, ExceptT.wp_monadLift_StateT_Demonic,
    StateT.wp_assume_eq] at ht
  obtain ⟨⟨ha, hk⟩, ⟨hr, hl⟩, hq⟩ := ht
  have ha : t.regs.get64 .rsp = pa := ha trivial
  have hg : retOk r₀ ra t := ⟨ha.trans hr, by rw [MachineData.retAddr_eq, ha]; exact hl⟩
  rw [wp_modifyIf]
  refine ⟨hg, ?_⟩
  rw [Concretization.post_pi]
  refine ⟨(), hk hg, ?_⟩
  simp only [ofStateRepr_pred, hf]
  exact hq

@[ascend] theorem wrp_modifyIf_stay {Q : Unit → PUnit → MachineData → Prop} (r₀ pa : BitVec 64) :
    (fun t => t.regs.get64 .rsp ≐ pa ∧ (stayIn r₀ t = true → Q () () t))
      ⊑ wrp (ofStateRepr MachineData.dmem)
          (modifyIf (fun s => stayIn r₀ s = true) id : BlockM MachineData Unit)
          (do StateT.assume (fun (_ : DataMem) => stayAt r₀ pa = true) : BlockM DataMem PUnit)
          Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, ExceptT.wp_monadLift_StateT_Demonic,
    StateT.wp_assume_eq] at ht
  obtain ⟨⟨ha, hk⟩, hl, hq⟩ := ht
  have ha : t.regs.get64 .rsp = pa := ha trivial
  have hg : stayIn r₀ t = true := by rw [stayIn, ha]; exact hl
  rw [wp_modifyIf]
  refine ⟨hg, ?_⟩
  rw [Concretization.post_pi]
  exact ⟨(), hk hg, hq⟩

@[ascend] theorem wrp_modifyIf_assume {Q : Unit → PUnit → MachineData → Prop}
    (a : MachineData → BitVec 64) (f : MachineData → MachineData) (pa : BitVec 64)
    (hf : ∀ t, (f t).dmem = t.dmem) :
    (fun t => a t ≐ pa ∧ (loadOk 8 a t → Q () () (f t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (loadOk 8 a) f : BlockM MachineData Unit)
          (do StateT.assume (fun m => (Mem.loadInt m pa 8).isSome = true) : BlockM DataMem PUnit)
          Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, ExceptT.wp_monadLift_StateT_Demonic,
    StateT.wp_assume_eq] at ht
  obtain ⟨⟨ha, hk⟩, hl, hq⟩ := ht
  have ha : a t = pa := ha trivial
  have hg : loadOk 8 a t := by rw [loadOk, ha]; exact hl
  rw [wp_modifyIf]
  refine ⟨hg, ?_⟩
  rw [Concretization.post_pi]
  refine ⟨(), hk hg, ?_⟩
  simp only [ofStateRepr_pred, hf]
  exact hq

end


end Ascent.Kraken
