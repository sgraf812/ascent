import Demo.Regs
import Demo.Words

/-!
# Arrays in the data memory

A program over the data memory refines a program over an array of words, under the
concretization `ofStateRepr (outView p n)` that reads the `n` words at the base address `p` as the
abstract state. The program reads further arrays as parameters: the hypothesis `q ≐ₐ a` names the
array at the base address `q` as the parameter `a`, and the load rule reads `a[i]!` where the
concrete program loads the word at `q + v * 8` and `v ≐ₙ i`: the word `v` holds the number `i`. A
store into the written array becomes `set!` at the index `i`. A load and a store keep the guards of
the memory steps and the bound of the index as verification conditions.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr ofStateRepr_pred)

namespace Distillery.Kraken

/-- The `n` words of `w` bytes at the base address `p` as an array of `b`-bit vectors. -/
def outView (w b : Nat) (p : BitVec 64) (n : Nat) (m : DataMem) : Array (BitVec b) :=
  (words w b m p n).toArray

@[grind =] theorem size_words_toArray (m : DataMem) (p : BitVec 64) (n : Nat) : (words 8 64 m p n).toArray.size = n := by
  simp [words]

@[grind →] theorem words_eq_of_outView {w b : Nat} {p : BitVec 64} {n : Nat} {m : DataMem}
    {l : List (BitVec b)} (h : outView w b p n m = l.toArray) : words w b m p n = l := by
  simpa only [outView, List.toList_toArray] using congrArg Array.toList h

@[simp, grind =] theorem size_outView : (outView w b p n m).size = n := by
  simp [outView, words]

/-- The base address `p` names the array `a` of the abstract program. -/
def ArrayBase {α : Type} (_ : BitVec 64) (_ : Array α) : Prop := True

@[grind norm] theorem ArrayBase_eq {α : Type} {a : Array α} : ArrayBase p a = True := rfl

/-- `q ≐ₐ a`: the base address `q` names the array parameter `a`. -/
scoped notation:50 q:51 " ≐ₐ " a:51 => PureRefinement q a True ArrayBase

/-- `Scaled w x j`: the byte offset `x` addresses the word at index `j` of an array of `w`-byte
words. -/
def Scaled (w : Nat) (x : BitVec 64) (j : Nat) : Prop := x = BitVec.ofNat 64 j * BitVec.ofNat 64 w

@[distill_pure] theorem absS_mul {x : BitVec 64} {j w : Nat} {P : Prop}
    (h : PureRefinement x j P WordNat) : PureRefinement (x * BitVec.ofNat 64 w) j P (Scaled w) :=
  fun hp => by rw [Scaled, h hp]

theorem CondCode.cmp_c_eq_true (a b : BitVec 64) : (CondCode.c.cmp a b = true) = (a < b) := by
  simp [CondCode.cmp, BitVec.ult, BitVec.lt_def]

attribute [grind =] Nat.blt_eq Nat.ble_eq

@[distill_pure high] theorem absN_cmp_c {a b : BitVec 64} {n m : Nat} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a n P₁ WordNat) (h₂ : PureRefinement b m P₂ WordNat) :
    PureRefinement (CondCode.c.cmp a b) (Nat.blt n m) (P₁ ∧ P₂ ∧ n < 2 ^ 64 ∧ m < 2 ^ 64) Eq :=
  fun ⟨hp₁, hp₂, hn, hm⟩ => by
    rw [Bool.eq_iff_iff, CondCode.cmp_c_eq_true, h₁ hp₁, h₂ hp₂, Nat.blt_eq, BitVec.lt_def,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm]

theorem WordNat.cmp_c_eq {x y : BitVec 64} {i j : Nat} (hx : WordNat x i) (hy : WordNat y j)
    (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) : (CondCode.c.cmp x y = true) = (i < j) := by
  rw [absN_cmp_c (PureRefinement.of_rel hx) (PureRefinement.of_rel hy) ⟨trivial, trivial, hi, hj⟩,
    Nat.blt_eq]

grind_pattern WordNat.cmp_c_eq => WordNat x i, WordNat y j, CondCode.c.cmp x y

/-! ## Words -/

section
variable {m : DataMem} {p q : BitVec 64} {n w b : Nat}

theorem word_eq_getElem {arr : Array (BitVec b)} (h : words w b m p arr.size = arr.toList) {k : Nat}
    (hk : k < arr.size) : word w b m p k = arr[k]! := by
  have h' := congrArg (fun l => l[k]?) h
  simp only [words, List.getElem?_ofFn, Array.getElem?_toList] at h'
  rw [dite_eq_left hk, Array.getElem?_eq_getElem hk] at h'
  rw [getElem!_pos arr k hk]
  exact Option.some.inj h'

theorem word_storeInt_self (hw : w ≤ 8) (hb : b = 8 * w) (k : Nat) (v : BitVec 64) :
    word w b (Mem.storeInt m (cell w p k) w v.toInt) p k = v.setWidth b := by
  rw [word, Mem.loadInt_storeInt _ _ _ _ (by omega), Option.get!_some,
    BitVec.ofInt_ofBytes_toBytes b w hb, ← BitVec.signExtend,
    BitVec.signExtend_eq_setWidth_of_le _ (by omega)]

theorem words_storeInt_self (hw : w ≤ 8) (hb : b = 8 * w) {k : Nat} (hk : k < n) (hn : n < 2 ^ 61)
    (v : BitVec 64) :
    words w b (Mem.storeInt m (cell w p k) w v.toInt) p n = (words w b m p n).set k (v.setWidth b) := by
  apply List.ext_getElem
  · simp [words]
  intro j h₁ h₂
  simp only [words, List.length_ofFn] at h₁
  simp only [words, List.getElem_ofFn, List.getElem_set]
  split
  · subst_vars
    exact word_storeInt_self hw rfl j v
  · rename_i hjk
    rw [word, Mem.loadInt_storeInt_of_disjoint (cell_disjoint hw h₁ hk (Ne.symm hjk) hn) _]
    rfl

theorem words_storeInt_of_disjoint (hw : w ≤ 8) {k nq : Nat}
    (hd : Mem.Blocks.Disjoint [(q, w * nq)] [(p, w * n)]) (hk : k < nq) (hq : nq < 2 ^ 61)
    (hn : n < 2 ^ 61) (v : Int) :
    words w b (Mem.storeInt m (cell w q k) w v) p n = words w b m p n := by
  apply List.ext_getElem
  · simp [words]
  intro j h₁ _
  simp only [words, List.length_ofFn] at h₁
  simp only [words, List.getElem_ofFn]
  rw [word, Mem.loadInt_storeInt_of_disjoint
    (Mem.Blocks.Disjoint.of_inside' hd (cell_inside hw h₁ hn) (cell_inside hw hk hq)) _]
  rfl

theorem outView_storeInt (hw : w ≤ 8) (hb : b = 8 * w) {k : Nat} (hk : k < n) (hn : n < 2 ^ 61)
    (v : BitVec 64) :
    outView w b p n (Mem.storeInt m (cell w p k) w v.toInt) = (outView w b p n m).set! k (v.setWidth b) := by
  rw [outView, outView, words_storeInt_self hw hb hk hn, Array.set!_eq_setIfInBounds,
    List.setIfInBounds_toArray]

end

/-! ## Layouts

`ArrayLayout w b ins o n m` states the memory `m` of a program that writes the array of `n` words of
`w` bytes at `o`, read as `b`-bit vectors: each input `(p, a)` of `ins` holds the array `a` at `p`,
and the written array is mapped and apart from the inputs. A store into the written array keeps the
layout. -/

/-- The array `a` lies at `p`, apart from the written array of `n` words at `o`. -/
structure InputAt (w b : Nat) (m : DataMem) (o : BitVec 64) (n : Nat) (p : BitVec 64)
    (a : Array (BitVec b)) : Prop where
  len : a.size < 2 ^ 61
  words : words w b m p a.size = a.toList
  mapped : Mem.Mapped [(p, w * a.size)] m
  disj : Mem.Blocks.Disjoint [(o, w * n)] [(p, w * a.size)]

def Inputs (w b : Nat) (m : DataMem) (o : BitVec 64) (n : Nat) :
    List (BitVec 64 × Array (BitVec b)) → Prop
  | [] => True
  | (p, a) :: ins => InputAt w b m o n p a ∧ Inputs w b m o n ins

structure ArrayLayout (w b : Nat) (ins : List (BitVec 64 × Array (BitVec b))) (o : BitVec 64)
    (n : Nat) (m : DataMem) : Prop where
  width : w ≤ 8
  bits : b = 8 * w
  len : n < 2 ^ 61
  mapped : Mem.Mapped [(o, w * n)] m
  inputs : Inputs w b m o n ins

attribute [grind →] InputAt.len InputAt.words InputAt.mapped InputAt.disj ArrayLayout.width
  ArrayLayout.bits ArrayLayout.len ArrayLayout.mapped ArrayLayout.inputs

section
variable {w b : Nat} {m : DataMem} {o : BitVec 64} {n : Nat}

@[grind =] theorem Inputs.nil : Inputs w b m o n [] = True := rfl
@[grind =] theorem Inputs.cons (p : BitVec 64) (a : Array (BitVec b)) ins :
    Inputs w b m o n ((p, a) :: ins) = (InputAt w b m o n p a ∧ Inputs w b m o n ins) := rfl

variable {k : Nat} (hw : w ≤ 8) (hk : k < n) (hn : n < 2 ^ 61) (x : Int)
include hw hk hn

theorem InputAt.storeInt {p : BitVec 64} {a : Array (BitVec b)} (h : InputAt w b m o n p a) :
    InputAt w b (Mem.storeInt m (cell w o k) w x) o n p a where
  len := h.len
  words := by rw [words_storeInt_of_disjoint hw h.disj hk hn h.len]; exact h.words
  mapped := Mem.Mapped.storeInt h.mapped _ _ _
  disj := h.disj

theorem Inputs.storeInt : ∀ {ins : List (BitVec 64 × Array (BitVec b))}, Inputs w b m o n ins →
    Inputs w b (Mem.storeInt m (cell w o k) w x) o n ins
  | [], _ => trivial
  | (_, _) :: _, ⟨h, hs⟩ => ⟨h.storeInt hw hk hn x, Inputs.storeInt hs⟩

end

theorem ArrayLayout.storeInt_cell {w b : Nat} {ins : List (BitVec 64 × Array (BitVec b))}
    {o : BitVec 64} {n : Nat} {m : DataMem} (h : ArrayLayout w b ins o n m)
    {k : Nat} (hk : k < n) (x : Int) :
    ArrayLayout w b ins o n (Mem.storeInt m (cell w o k) w x) :=
  ⟨h.width, h.bits, h.len, Mem.Mapped.storeInt h.mapped _ _ _, h.inputs.storeInt h.width hk h.len x⟩

grind_pattern ArrayLayout.storeInt_cell => Mem.storeInt m (cell w o k) w x, ArrayLayout w b ins o n m

/-! ## Steps -/

theorem wp_modify {σ : Type} (f : σ → σ) (Q : Unit → σ → Prop) (E : (Int64 → σ → Prop) × EStack⟨⟩)
    (s : σ) : wp (modify f : BlockM σ Unit) Q E s = Q () (f s) := by
  rw [wp_BlockM_eq]
  rfl


section
variable {σa : Type} {view : DataMem → σa}
  {E : (Int64 → Int64 → DataMem → Prop) × EStack⟨⟩}

@[distill] theorem wrp_load_getElem {Q : BitVec 64 → BitVec 64 → DataMem → Prop}
    (w b : Nat) (p o : BitVec 64) (arr : Array (BitVec b)) (j : Nat) (P : Prop) (_harr : p ≐ₐ arr)
    (hij : PureRefinement o j P (Scaled w)) :
    (fun m => P ∧ w ≤ 8 ∧ b = 8 * w ∧
      words w b m p arr.size = arr.toList ∧ Mem.Mapped [(p, w * arr.size)] m ∧ j < arr.size ∧
      arr.size < 2 ^ 61 ∧
      ∀ y, BitVec.ofInt 64 ((Mem.loadInt m (p + o) w).get! % 2 ^ (8 * w)) ≐ y →
        Q (BitVec.ofInt 64 ((Mem.loadInt m (p + o) w).get! % 2 ^ (8 * w))) y m)
      ⊑ wrp (ofStateRepr view) (load w (p + o))
          (pure ((arr[j]!).setWidth 64) : BlockM σa (BitVec 64)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at hm
  obtain ⟨⟨hP, hw, hb, hwd, hmap, hj, hn, hk⟩, hq⟩ := hm
  have hcell : p + o = cell w p j := by rw [hij hP]; rfl
  have hval : BitVec.ofInt 64 ((Mem.loadInt m (p + o) w).get! % 2 ^ (8 * w)) = (arr[j]!).setWidth 64 := by
    rw [hcell, ← word_eq_getElem hwd hj, word, setWidth_ofInt (by omega), hb]
  rw [wp_load, Concretization.post_pi]
  refine ⟨?_, (arr[j]!).setWidth 64, hk _ (PureRefinement.of_rel hval), ?_⟩
  · rw [hcell]
    exact Mem.Mapped.loadInt_isSome hmap (cell_inside hw hj hn)
  · simp only [ofStateRepr_pred]
    exact hq

@[grind =] theorem Int64.toInt_neg_one : (-1 : Int64).toInt = -((1 : Nat) : Int) := rfl

theorem cell_pred {w j : Nat} (p : BitVec 64) (hj : 0 < j) :
    p + BitVec.ofNat 64 j * BitVec.ofNat 64 w + BitVec.ofInt 64 (-(w : Int)) = cell w p (j - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [cell, Nat.add_sub_cancel, BitVec.ofNat_add, BitVec.ofInt_neg, BitVec.ofInt_natCast]
  grind

/-- `Index w p c j`: the address `c` is the cell `j` of the array of `w`-byte words at `p`. -/
def Index (w : Nat) (p : BitVec 64) (c : BitVec 64) (j : Nat) : Prop := c = cell w p j

section
variable {w : Nat} {p c x : BitVec 64} {j i : Nat} {P P₁ P₂ : Prop}

@[distill_pure] theorem absI_base : PureRefinement p 0 True (Index w p) :=
  PureRefinement.of_rel (by simp [Index, cell])

@[distill_pure] theorem absI_add_w (h : PureRefinement c j P (Index w p)) :
    PureRefinement (c + BitVec.ofNat 64 w) (j + 1) P (Index w p) := fun hp => by
  have e : c = cell w p j := h hp
  rw [Index, e]
  simp only [cell, BitVec.ofNat_add]
  grind

@[distill_pure low] theorem absI_sub {k : Nat} (h : PureRefinement c j P (Index w p)) :
    PureRefinement (c + BitVec.ofNat 64 k) (j - 1) (P ∧ 0 < j ∧ k + w = 2 ^ 64) (Index w p) :=
  fun ⟨hp, hj, hk⟩ => by
    have e : c = cell w p j := h hp
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h2 : BitVec.ofNat 64 k + BitVec.ofNat 64 w = 0#64 := by
      rw [← BitVec.ofNat_add, hk]
      decide +kernel
    rw [Index, e, Nat.add_sub_cancel]
    simp only [cell, BitVec.ofNat_add]
    grind

@[distill_pure] theorem absI_add_scaled (h₁ : PureRefinement c j P₁ (Index w p))
    (h₂ : PureRefinement x i P₂ WordNat) :
    PureRefinement (c + x * BitVec.ofNat 64 w) (j + i) (P₁ ∧ P₂) (Index w p) := fun ⟨hp₁, hp₂⟩ => by
  have e₁ : c = cell w p j := h₁ hp₁
  have e₂ : x = BitVec.ofNat 64 i := h₂ hp₂
  rw [Index, e₁, e₂]
  simp only [cell, BitVec.ofNat_add]
  grind

end


@[distill default + 1] theorem wrp_load_getElem_pred {Q : BitVec 64 → BitVec 64 → DataMem → Prop}
    (w b : Nat) (p o : BitVec 64) (d : Int) (arr : Array (BitVec b)) (j : Nat) (P : Prop) (_harr : p ≐ₐ arr)
    (hij : PureRefinement o j P (Scaled w)) :
    (fun m => P ∧ 0 < j ∧ d = -(w : Int) ∧ w ≤ 8 ∧
      b = 8 * w ∧ words w b m p arr.size = arr.toList ∧ Mem.Mapped [(p, w * arr.size)] m ∧
      j - 1 < arr.size ∧ arr.size < 2 ^ 61 ∧
      ∀ y, BitVec.ofInt 64 ((Mem.loadInt m (p + o + BitVec.ofInt 64 d) w).get! % 2 ^ (8 * w)) ≐ y →
        Q (BitVec.ofInt 64 ((Mem.loadInt m (p + o + BitVec.ofInt 64 d) w).get! % 2 ^ (8 * w))) y m)
      ⊑ wrp (ofStateRepr view) (load w (p + o + BitVec.ofInt 64 d))
          (pure ((arr[j - 1]!).setWidth 64) : BlockM σa (BitVec 64)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at hm
  obtain ⟨⟨hP, hj0, hd, hw, hb, hwd, hmap, hj, hn, hk⟩, hq⟩ := hm
  have hcell : p + o + BitVec.ofInt 64 d = cell w p (j - 1) := by rw [hij hP, hd, cell_pred p hj0]
  have hval : BitVec.ofInt 64 ((Mem.loadInt m (p + o + BitVec.ofInt 64 d) w).get! % 2 ^ (8 * w)) =
      (arr[j - 1]!).setWidth 64 := by
    rw [hcell, ← word_eq_getElem hwd hj, word, setWidth_ofInt (by omega), hb]
  rw [wp_load, Concretization.post_pi]
  refine ⟨?_, (arr[j - 1]!).setWidth 64, hk _ (PureRefinement.of_rel hval), ?_⟩
  · rw [hcell]
    exact Mem.Mapped.loadInt_isSome hmap (cell_inside hw hj hn)
  · simp only [ofStateRepr_pred]
    exact hq

@[distill] theorem wrp_store_set {Q : Unit → Unit → DataMem → Prop} (w b : Nat) (p o v v' : BitVec 64)
    (n j : Nat) (P : Prop) (hij : PureRefinement o j P (Scaled w)) :
    (fun m => v ≐ v' ∧ P ∧ w ≤ 8 ∧ b = 8 * w ∧ j < n ∧ n < 2 ^ 61 ∧
      Mem.Mapped [(p, w * n)] m ∧
      Q () () (Mem.storeInt m (cell w p j) w v.toInt))
      ⊑ wrp (ofStateRepr (outView w b p n)) (store w (p + o) v)
          (modify fun o => o.set! j (v'.setWidth b) : BlockM (Array (BitVec b)) Unit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_modify] at hm
  obtain ⟨⟨hv, hP, hw, hb, hj, hn, hmap, hk⟩, hq⟩ := hm
  have hv : v = v' := hv trivial
  have hcell : p + o = cell w p j := by rw [hij hP]; rfl
  rw [wp_store, Concretization.post_pi, hcell]
  refine ⟨Mem.Mapped.loadInt_isSome hmap (cell_inside hw hj hn), (), hk, ?_⟩
  simp only [ofStateRepr_pred]
  rw [outView_storeInt hw hb hj hn, hv]
  exact hq

@[distill default + 1] theorem wrp_store_set_pred {Q : Unit → Unit → DataMem → Prop} (w b : Nat)
    (p o v v' : BitVec 64) (d : Int) (n j : Nat) (P : Prop) (hij : PureRefinement o j P (Scaled w)) :
    (fun m => v ≐ v' ∧ P ∧ 0 < j ∧ d = -(w : Int) ∧ w ≤ 8 ∧
      b = 8 * w ∧ j - 1 < n ∧ n < 2 ^ 61 ∧ Mem.Mapped [(p, w * n)] m ∧
      Q () () (Mem.storeInt m (cell w p (j - 1)) w v.toInt))
      ⊑ wrp (ofStateRepr (outView w b p n)) (store w (p + o + BitVec.ofInt 64 d) v)
          (modify fun o => o.set! (j - 1) (v'.setWidth b) : BlockM (Array (BitVec b)) Unit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_modify] at hm
  obtain ⟨⟨hv, hP, hj0, hd, hw, hb, hj, hn, hmap, hk⟩, hq⟩ := hm
  have hv : v = v' := hv trivial
  have hcell : p + o + BitVec.ofInt 64 d = cell w p (j - 1) := by rw [hij hP, hd, cell_pred p hj0]
  rw [wp_store, Concretization.post_pi, hcell]
  refine ⟨Mem.Mapped.loadInt_isSome hmap (cell_inside hw hj hn), (), hk, ?_⟩
  simp only [ofStateRepr_pred]
  rw [outView_storeInt hw hb hj hn, hv]
  exact hq

@[distill default - 1] theorem wrp_load_get {Q : BitVec 64 → BitVec 64 → DataMem → Prop} (w b : Nat) (p c : BitVec 64)
    (n j : Nat) (P : Prop) (hij : PureRefinement c j P (Index w p)) :
    (fun m => P ∧ w ≤ 8 ∧ b = 8 * w ∧ j < n ∧ n < 2 ^ 61 ∧
      Mem.Mapped [(p, w * n)] m ∧
      ∀ y, BitVec.ofInt 64 ((Mem.loadInt m c w).get! % 2 ^ (8 * w)) ≐ y →
        Q (BitVec.ofInt 64 ((Mem.loadInt m c w).get! % 2 ^ (8 * w))) y m)
      ⊑ wrp (ofStateRepr (outView w b p n)) (load w c)
          (get >>= fun arr : Array (BitVec b) => pure ((arr[j]!).setWidth 64) : BlockM (Array (BitVec b)) (BitVec 64))
          Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_get_bind, WPMonadExact.wp_pure_eq] at hm
  obtain ⟨⟨hP, hw, hb, hj, hn, hmap, hk⟩, hq⟩ := hm
  have hcell : c = cell w p j := hij hP
  have hwd : words w b m p (outView w b p n m).size = (outView w b p n m).toList := by
    rw [size_outView]
    simp only [outView, List.toList_toArray]
  have hval : BitVec.ofInt 64 ((Mem.loadInt m c w).get! % 2 ^ (8 * w))
      = ((outView w b p n m)[j]!).setWidth 64 := by
    rw [hcell, ← word_eq_getElem hwd (by simpa only [size_outView] using hj), word,
      setWidth_ofInt (by omega), hb]
  rw [wp_load, Concretization.post_pi]
  refine ⟨?_, _, hk _ (PureRefinement.of_rel hval), ?_⟩
  · rw [hcell]
    exact Mem.Mapped.loadInt_isSome hmap (cell_inside hw hj hn)
  · simp only [ofStateRepr_pred]
    exact hq

@[distill default - 1] theorem wrp_store_set_at {Q : Unit → Unit → DataMem → Prop} (w b : Nat) (p c v v' : BitVec 64)
    (n j : Nat) (P : Prop) (hij : PureRefinement c j P (Index w p)) :
    (fun m => v ≐ v' ∧ P ∧ w ≤ 8 ∧ b = 8 * w ∧ j < n ∧ n < 2 ^ 61 ∧
      Mem.Mapped [(p, w * n)] m ∧
      Q () () (Mem.storeInt m (cell w p j) w v.toInt))
      ⊑ wrp (ofStateRepr (outView w b p n)) (store w c v)
          (modify fun o => o.set! j (v'.setWidth b) : BlockM (Array (BitVec b)) Unit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_modify] at hm
  obtain ⟨⟨hv, hP, hw, hb, hj, hn, hmap, hk⟩, hq⟩ := hm
  have hv : v = v' := hv trivial
  have hcell : c = cell w p j := hij hP
  rw [wp_store, Concretization.post_pi, hcell]
  refine ⟨Mem.Mapped.loadInt_isSome hmap (cell_inside hw hj hn), (), hk, ?_⟩
  simp only [ofStateRepr_pred]
  rw [outView_storeInt hw hb hj hn, hv]
  exact hq

end

end Distillery.Kraken

/-! ## `Array.zipWith` from its elements -/

namespace Array

theorem eq_zipWith_of_getElem! {α β γ : Type} [Inhabited α] [Inhabited β] [Inhabited γ]
    {o : Array γ} {a : Array α} {b : Array β} {f : α → β → γ} (ho : o.size = a.size)
    (hb : b.size = a.size) (h : ∀ i < a.size, o[i]! = f a[i]! b[i]!) :
    o = Array.zipWith f a b := by
  apply Array.ext
  · simp [ho, hb]
  · intro i h₁ _
    rw [Array.getElem_zipWith]
    have hi := h i (ho ▸ h₁)
    rwa [getElem!_pos o i h₁, getElem!_pos a i (by omega), getElem!_pos b i (by omega)] at hi

theorem set!_eq_zipWith {α β γ : Type} [Inhabited α] [Inhabited β] [Inhabited γ]
    {o : Array γ} {a : Array α} {b : Array β} {f : α → β → γ} {k : Nat} (ho : o.size = a.size)
    (hb : b.size = a.size) (hk : k + 1 = a.size) (h : ∀ i < k, o[i]! = f a[i]! b[i]!) :
    o.set! k (f a[k]! b[k]!) = Array.zipWith f a b := by
  refine eq_zipWith_of_getElem! (by simp [ho]) hb fun i hi => ?_
  by_cases hik : k = i
  · subst hik; exact Array.getElem!_set!_self _ _ _ (by omega)
  · rw [Array.getElem!_set!_ne _ _ _ _ hik]; exact h i (by omega)

grind_pattern set!_eq_zipWith => o.set! k (f a[k]! b[k]!), Array.zipWith f a b

theorem eq_of_getElem! {α : Type} [Inhabited α] {o a : Array α} (ho : o.size = a.size)
    (h : ∀ i < a.size, o[i]! = a[i]!) : o = a := by
  apply Array.ext ho
  intro i h₁ h₂
  have hi := h i h₂
  rwa [getElem!_pos o i h₁, getElem!_pos a i h₂] at hi

theorem set!_eq_of_getElem! {α : Type} [Inhabited α] {o a : Array α} {k : Nat}
    (ho : o.size = a.size) (hk : k + 1 = a.size) (h : ∀ i < k, o[i]! = a[i]!) :
    o.set! k a[k]! = a := by
  refine eq_of_getElem! (by simp [ho]) fun i hi => ?_
  by_cases hik : k = i
  · subst hik; exact Array.getElem!_set!_self _ _ _ (by omega)
  · rw [Array.getElem!_set!_ne _ _ _ _ hik]; exact h i (by omega)

grind_pattern set!_eq_of_getElem! => o.set! k a[k]!

end Array

