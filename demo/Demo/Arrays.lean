import Demo.Lift
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

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Kraken

/-- The `n` words of `w` bytes at the base address `p` as an array of `b`-bit vectors. -/
def outView (w b : Nat) (p : BitVec 64) (n : Nat) (m : DataMem) : Array (BitVec b) :=
  (words w b m p n).toArray

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

@[ascend_pure] theorem absS_mul {x : BitVec 64} {j w : Nat} {P : Prop}
    (h : PureRefinement x j P WordNat) : PureRefinement (x * BitVec.ofNat 64 w) j P (Scaled w) :=
  fun hp => by rw [Scaled, h hp]

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

theorem loadInt_storeInt_cell_of_disjoint (hw : w ≤ 8) {k : Nat} {x : BitVec 64}
    (hd : Mem.Blocks.Disjoint [(x, 8)] [(q, w * n)]) (hk : k < n) (hn : n < 2 ^ 61) (v : Int) :
    Mem.loadInt (Mem.storeInt m (cell w q k) w v) x 8 = Mem.loadInt m x 8 :=
  Mem.loadInt_storeInt_of_disjoint (Mem.Blocks.Disjoint.of_inside_right_pair hd (cell_inside hw hk hn)) v

end

/-! ## Layouts

`ArrayLayout w b ins o n rsv m` states the memory `m` of a program that writes the array of `n`
words of `w` bytes at `o`, read as `b`-bit vectors: each input `(p, a)` of `ins` holds the array `a`
at `p`, each reserved word `(p, ra)` of `rsv`, such as a return slot, holds the address `ra`, and
the written array is mapped and apart from the inputs and from the reserved words. A store into the written array keeps
the layout. -/

/-- The array `a` lies at `p`, apart from the written array of `n` words at `o`. -/
structure InputAt (w b : Nat) (m : DataMem) (o : BitVec 64) (n : Nat) (p : BitVec 64)
    (a : Array (BitVec b)) : Prop where
  len : a.size < 2 ^ 61
  words : words w b m p a.size = a.toList
  mapped : Mem.Mapped [(p, w * a.size)] m
  disj : Mem.Blocks.Disjoint [(o, w * n)] [(p, w * a.size)]

/-- The word at `p` holds the address `ra` and lies apart from the written array of `n` words at
`o`. -/
structure ReservedAt (w : Nat) (m : DataMem) (o : BitVec 64) (n : Nat) (p : BitVec 64) (ra : Int64) :
    Prop where
  retAddr : retAddrAt m p = some ra
  disj : Mem.Blocks.Disjoint [(p, 8)] [(o, w * n)]

theorem ReservedAt.loadInt_isSome {w : Nat} {m : DataMem} {o : BitVec 64} {n : Nat} {p : BitVec 64}
    {ra : Int64} (h : ReservedAt w m o n p ra) : (Mem.loadInt m p 8).isSome = true := by
  have := h.retAddr
  simp only [retAddrAt] at this
  cases hl : Mem.loadInt m p 8 <;> simp_all

def Inputs (w b : Nat) (m : DataMem) (o : BitVec 64) (n : Nat) :
    List (BitVec 64 × Array (BitVec b)) → Prop
  | [] => True
  | (p, a) :: ins => InputAt w b m o n p a ∧ Inputs w b m o n ins

def Reserved (w : Nat) (m : DataMem) (o : BitVec 64) (n : Nat) : List (BitVec 64 × Int64) → Prop
  | [] => True
  | (p, ra) :: rsv => ReservedAt w m o n p ra ∧ Reserved w m o n rsv

structure ArrayLayout (w b : Nat) (ins : List (BitVec 64 × Array (BitVec b))) (o : BitVec 64)
    (n : Nat) (rsv : List (BitVec 64 × Int64)) (m : DataMem) : Prop where
  width : w ≤ 8
  bits : b = 8 * w
  len : n < 2 ^ 61
  mapped : Mem.Mapped [(o, w * n)] m
  inputs : Inputs w b m o n ins
  reserved : Reserved w m o n rsv

attribute [grind →] InputAt.len InputAt.words InputAt.mapped InputAt.disj ReservedAt.retAddr
  ReservedAt.loadInt_isSome
  ReservedAt.disj ArrayLayout.width ArrayLayout.bits ArrayLayout.len ArrayLayout.mapped
  ArrayLayout.inputs ArrayLayout.reserved

section
variable {w b : Nat} {m : DataMem} {o : BitVec 64} {n : Nat}

@[grind =] theorem Inputs.nil : Inputs w b m o n [] = True := rfl
@[grind =] theorem Inputs.cons (p : BitVec 64) (a : Array (BitVec b)) ins :
    Inputs w b m o n ((p, a) :: ins) = (InputAt w b m o n p a ∧ Inputs w b m o n ins) := rfl
@[grind =] theorem Reserved.nil : Reserved w m o n [] = True := rfl
@[grind =] theorem Reserved.cons (p : BitVec 64) (ra : Int64) rsv :
    Reserved w m o n ((p, ra) :: rsv) = (ReservedAt w m o n p ra ∧ Reserved w m o n rsv) := rfl

variable {k : Nat} (hw : w ≤ 8) (hk : k < n) (hn : n < 2 ^ 61) (x : Int)
include hw hk hn

theorem InputAt.storeInt {p : BitVec 64} {a : Array (BitVec b)} (h : InputAt w b m o n p a) :
    InputAt w b (Mem.storeInt m (cell w o k) w x) o n p a where
  len := h.len
  words := by rw [words_storeInt_of_disjoint hw h.disj hk hn h.len]; exact h.words
  mapped := Mem.Mapped.storeInt h.mapped _ _ _
  disj := h.disj

theorem ReservedAt.storeInt {p : BitVec 64} {ra : Int64} (h : ReservedAt w m o n p ra) :
    ReservedAt w (Mem.storeInt m (cell w o k) w x) o n p ra :=
  ⟨by rw [retAddrAt, loadInt_storeInt_cell_of_disjoint hw h.disj hk hn]; exact h.retAddr, h.disj⟩

theorem Inputs.storeInt : ∀ {ins : List (BitVec 64 × Array (BitVec b))}, Inputs w b m o n ins →
    Inputs w b (Mem.storeInt m (cell w o k) w x) o n ins
  | [], _ => trivial
  | (_, _) :: _, ⟨h, hs⟩ => ⟨h.storeInt hw hk hn x, Inputs.storeInt hs⟩

theorem Reserved.storeInt : ∀ {rsv}, Reserved w m o n rsv →
    Reserved w (Mem.storeInt m (cell w o k) w x) o n rsv
  | [], _ => trivial
  | (_, _) :: _, ⟨h, hs⟩ => ⟨h.storeInt hw hk hn x, Reserved.storeInt hs⟩

end

theorem ArrayLayout.storeInt_cell {w b : Nat} {ins : List (BitVec 64 × Array (BitVec b))}
    {o : BitVec 64} {n : Nat} {rsv : List (BitVec 64 × Int64)} {m : DataMem} (h : ArrayLayout w b ins o n rsv m)
    {k : Nat} (hk : k < n) (x : Int) :
    ArrayLayout w b ins o n rsv (Mem.storeInt m (cell w o k) w x) :=
  ⟨h.width, h.bits, h.len, Mem.Mapped.storeInt h.mapped _ _ _, h.inputs.storeInt h.width hk h.len x,
    h.reserved.storeInt h.width hk h.len x⟩

grind_pattern ArrayLayout.storeInt_cell => Mem.storeInt m (cell w o k) w x, ArrayLayout w b ins o n rsv m

/-! ## Steps -/

theorem wp_modify {σ : Type} (f : σ → σ) (Q : Unit → σ → Prop) (E : (Int64 → σ → Prop) × EStack⟨⟩)
    (s : σ) : wp (modify f : BlockM σ Unit) Q E s = Q () (f s) := by
  rw [wp_BlockM_eq]
  rfl


section
variable {σa : Type} {view : DataMem → σa}
  {E : (Int64 → Int64 → DataMem → Prop) × EStack⟨⟩}

@[ascend] theorem wrp_load_getElem {Q : BitVec 64 → BitVec 64 → DataMem → Prop}
    (w b : Nat) (p o : BitVec 64) (arr : Array (BitVec b)) (j : Nat) (P : Prop) :
    (fun m => p ≐ₐ arr ∧ PureRefinement o j P (Scaled w) ∧ P ∧ w ≤ 8 ∧ b = 8 * w ∧
      words w b m p arr.size = arr.toList ∧ Mem.Mapped [(p, w * arr.size)] m ∧ j < arr.size ∧
      arr.size < 2 ^ 61 ∧
      ∀ y, BitVec.ofInt 64 ((Mem.loadInt m (p + o) w).get! % 2 ^ (8 * w)) ≐ y →
        Q (BitVec.ofInt 64 ((Mem.loadInt m (p + o) w).get! % 2 ^ (8 * w))) y m)
      ⊑ wrp (ofStateRepr view) (load w (p + o))
          (pure ((arr[j]!).setWidth 64) : BlockM σa (BitVec 64)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at hm
  obtain ⟨⟨-, hij, hP, hw, hb, hwd, hmap, hj, hn, hk⟩, hq⟩ := hm
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

@[ascend default + 1] theorem wrp_load_getElem_pred {Q : BitVec 64 → BitVec 64 → DataMem → Prop}
    (w b : Nat) (p o : BitVec 64) (d : Int) (arr : Array (BitVec b)) (j : Nat) (P : Prop) :
    (fun m => p ≐ₐ arr ∧ PureRefinement o j P (Scaled w) ∧ P ∧ 0 < j ∧ d = -(w : Int) ∧ w ≤ 8 ∧
      b = 8 * w ∧ words w b m p arr.size = arr.toList ∧ Mem.Mapped [(p, w * arr.size)] m ∧
      j - 1 < arr.size ∧ arr.size < 2 ^ 61 ∧
      ∀ y, BitVec.ofInt 64 ((Mem.loadInt m (p + o + BitVec.ofInt 64 d) w).get! % 2 ^ (8 * w)) ≐ y →
        Q (BitVec.ofInt 64 ((Mem.loadInt m (p + o + BitVec.ofInt 64 d) w).get! % 2 ^ (8 * w))) y m)
      ⊑ wrp (ofStateRepr view) (load w (p + o + BitVec.ofInt 64 d))
          (pure ((arr[j - 1]!).setWidth 64) : BlockM σa (BitVec 64)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at hm
  obtain ⟨⟨-, hij, hP, hj0, hd, hw, hb, hwd, hmap, hj, hn, hk⟩, hq⟩ := hm
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

@[ascend] theorem wrp_store_set {Q : Unit → Unit → DataMem → Prop} (w b : Nat) (p o v v' : BitVec 64)
    (n j : Nat) (P : Prop) :
    (fun m => v ≐ v' ∧ PureRefinement o j P (Scaled w) ∧ P ∧ w ≤ 8 ∧ b = 8 * w ∧ j < n ∧ n < 2 ^ 61 ∧
      Mem.Mapped [(p, w * n)] m ∧
      Q () () (Mem.storeInt m (cell w p j) w v.toInt))
      ⊑ wrp (ofStateRepr (outView w b p n)) (store w (p + o) v)
          (modify fun o => o.set! j (v'.setWidth b) : BlockM (Array (BitVec b)) Unit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_modify] at hm
  obtain ⟨⟨hv, hij, hP, hw, hb, hj, hn, hmap, hk⟩, hq⟩ := hm
  have hv : v = v' := hv trivial
  have hcell : p + o = cell w p j := by rw [hij hP]; rfl
  rw [wp_store, Concretization.post_pi, hcell]
  refine ⟨Mem.Mapped.loadInt_isSome hmap (cell_inside hw hj hn), (), hk, ?_⟩
  simp only [ofStateRepr_pred]
  rw [outView_storeInt hw hb hj hn, hv]
  exact hq

@[ascend default + 1] theorem wrp_store_set_pred {Q : Unit → Unit → DataMem → Prop} (w b : Nat)
    (p o v v' : BitVec 64) (d : Int) (n j : Nat) (P : Prop) :
    (fun m => v ≐ v' ∧ PureRefinement o j P (Scaled w) ∧ P ∧ 0 < j ∧ d = -(w : Int) ∧ w ≤ 8 ∧
      b = 8 * w ∧ j - 1 < n ∧ n < 2 ^ 61 ∧ Mem.Mapped [(p, w * n)] m ∧
      Q () () (Mem.storeInt m (cell w p (j - 1)) w v.toInt))
      ⊑ wrp (ofStateRepr (outView w b p n)) (store w (p + o + BitVec.ofInt 64 d) v)
          (modify fun o => o.set! (j - 1) (v'.setWidth b) : BlockM (Array (BitVec b)) Unit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_modify] at hm
  obtain ⟨⟨hv, hij, hP, hj0, hd, hw, hb, hj, hn, hmap, hk⟩, hq⟩ := hm
  have hv : v = v' := hv trivial
  have hcell : p + o + BitVec.ofInt 64 d = cell w p (j - 1) := by rw [hij hP, hd, cell_pred p hj0]
  rw [wp_store, Concretization.post_pi, hcell]
  refine ⟨Mem.Mapped.loadInt_isSome hmap (cell_inside hw hj hn), (), hk, ?_⟩
  simp only [ofStateRepr_pred]
  rw [outView_storeInt hw hb hj hn, hv]
  exact hq

end

end Ascent.Kraken

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

