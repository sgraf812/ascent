import Demo.Lift
import Demo.Words

/-!
# Arrays in the data memory

A program over the data memory refines a program over an array of words, under the
concretization `ofStateRepr (outView p n)` that reads the `n` words at the base address `p` as the
abstract state. The program reads further arrays as parameters: the hypothesis `q ≐ₐ a` names the
array at the base address `q` as the parameter `a`, and the load rule reads `a[i]!` where the
concrete program loads the word at `q + i * 8`. A load and a store keep the guards of the memory
steps as verification conditions.

`wrp_forIn_diag_bind_unit` refines a loop to a loop with the same loop value. The relation `I` of
the loop states the layout of the memory in each iteration.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Kraken

/-- The `n` words at the base address `p` as an array. -/
def outView (p : BitVec 64) (n : Nat) (m : DataMem) : Array (BitVec 64) := (words m p n).toArray

/-- The base address `p` names the array `a` of the abstract program. -/
def ArrayBase (_ : BitVec 64) (_ : Array (BitVec 64)) : Prop := True

/-- `q ≐ₐ a`: the base address `q` names the array parameter `a`. -/
scoped notation:50 q:51 " ≐ₐ " a:51 => PureRefinement q a True ArrayBase

/-! ## Words -/

section
variable {m : DataMem} {p q : BitVec 64} {n : Nat}

theorem add_mul_eight (p i : BitVec 64) : p + i * 8#64 = cell p i.toNat := by
  simp only [cell, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

theorem word_eq_getElem {arr : Array (BitVec 64)} (h : words m p arr.size = arr.toList) {k : Nat}
    (hk : k < arr.size) : word m p k = arr[k]! := by
  have h' := congrArg (fun l => l[k]?) h
  simp only [words, List.getElem?_ofFn, Array.getElem?_toList] at h'
  rw [dite_eq_left hk, Array.getElem?_eq_getElem hk] at h'
  rw [getElem!_pos arr k hk]
  exact Option.some.inj h'

theorem word_storeInt_self (k : Nat) (v : BitVec 64) :
    word (Mem.storeInt m (cell p k) 8 v.toInt) p k = v := by
  rw [word, Mem.loadInt_storeInt_64, Option.get!_some, BitVec.ofInt_ofBytes_toBytes_64,
    BitVec.ofInt_toInt]

theorem words_storeInt_self {k : Nat} (hk : k < n) (hn : n < 2 ^ 61) (v : BitVec 64) :
    words (Mem.storeInt m (cell p k) 8 v.toInt) p n = (words m p n).set k v := by
  apply List.ext_getElem
  · simp [words]
  intro j h₁ h₂
  simp only [words, List.length_ofFn] at h₁
  simp only [words, List.getElem_ofFn, List.getElem_set]
  split
  · subst_vars
    exact word_storeInt_self j v
  · rename_i hjk
    rw [word, Mem.loadInt_storeInt_of_disjoint (cell_disjoint h₁ hk (Ne.symm hjk) hn) _]
    rfl

theorem words_storeInt_of_disjoint {k nq : Nat}
    (hd : Mem.Blocks.Disjoint [(q, 8 * nq)] [(p, 8 * n)]) (hk : k < nq) (hq : nq < 2 ^ 61)
    (hn : n < 2 ^ 61) (v : Int) : words (Mem.storeInt m (cell q k) 8 v) p n = words m p n := by
  apply List.ext_getElem
  · simp [words]
  intro j h₁ _
  simp only [words, List.length_ofFn] at h₁
  simp only [words, List.getElem_ofFn]
  rw [word, Mem.loadInt_storeInt_of_disjoint
    (Mem.Blocks.Disjoint.of_inside' hd (cell_inside h₁ hn) (cell_inside hk hq)) _]
  rfl

theorem outView_storeInt {k : Nat} (hk : k < n) (hn : n < 2 ^ 61) (v : BitVec 64) :
    outView p n (Mem.storeInt m (cell p k) 8 v.toInt) = (outView p n m).set! k v := by
  rw [outView, outView, words_storeInt_self hk hn, Array.set!_eq_setIfInBounds,
    List.setIfInBounds_toArray]

theorem loadInt_storeInt_cell_of_disjoint {k : Nat} {x : BitVec 64}
    (hd : Mem.Blocks.Disjoint [(x, 8)] [(q, 8 * n)]) (hk : k < n) (hn : n < 2 ^ 61) (v : Int) :
    Mem.loadInt (Mem.storeInt m (cell q k) 8 v) x 8 = Mem.loadInt m x 8 :=
  Mem.loadInt_storeInt_of_disjoint (Mem.Blocks.Disjoint.of_inside_right_pair hd (cell_inside hk hn)) v

end

/-! ## Layouts

`ArrayLayout ins o n rsv m` states the memory `m` of a program that writes the array of `n` words
at `o`: each input `(p, a)` of `ins` holds the array `a` at `p`, each reserved word of `rsv`, such
as a return slot, is mapped, and the written array is mapped and apart from the inputs and from the
reserved words. A store into the written array keeps the layout. -/

/-- The array `a` lies at `p`, apart from the written array of `n` words at `o`. -/
structure InputAt (m : DataMem) (o : BitVec 64) (n : Nat) (p : BitVec 64) (a : Array (BitVec 64)) :
    Prop where
  len : a.size < 2 ^ 61
  words : words m p a.size = a.toList
  mapped : Mem.Mapped [(p, 8 * a.size)] m
  disj : Mem.Blocks.Disjoint [(o, 8 * n)] [(p, 8 * a.size)]

/-- The word at `p` is mapped and apart from the written array of `n` words at `o`. -/
structure ReservedAt (m : DataMem) (o : BitVec 64) (n : Nat) (p : BitVec 64) : Prop where
  loadInt_isSome : (Mem.loadInt m p 8).isSome = true
  disj : Mem.Blocks.Disjoint [(p, 8)] [(o, 8 * n)]

def Inputs (m : DataMem) (o : BitVec 64) (n : Nat) : List (BitVec 64 × Array (BitVec 64)) → Prop
  | [] => True
  | (p, a) :: ins => InputAt m o n p a ∧ Inputs m o n ins

def Reserved (m : DataMem) (o : BitVec 64) (n : Nat) : List (BitVec 64) → Prop
  | [] => True
  | p :: rsv => ReservedAt m o n p ∧ Reserved m o n rsv

structure ArrayLayout (ins : List (BitVec 64 × Array (BitVec 64))) (o : BitVec 64) (n : Nat)
    (rsv : List (BitVec 64)) (m : DataMem) : Prop where
  len : n < 2 ^ 61
  mapped : Mem.Mapped [(o, 8 * n)] m
  inputs : Inputs m o n ins
  reserved : Reserved m o n rsv

attribute [grind →] InputAt.len InputAt.words InputAt.mapped InputAt.disj ReservedAt.loadInt_isSome
  ReservedAt.disj ArrayLayout.len ArrayLayout.mapped ArrayLayout.inputs ArrayLayout.reserved

section
variable {m : DataMem} {o : BitVec 64} {n : Nat}

@[grind =] theorem Inputs.nil : Inputs m o n [] = True := rfl
@[grind =] theorem Inputs.cons (p : BitVec 64) (a : Array (BitVec 64)) ins :
    Inputs m o n ((p, a) :: ins) = (InputAt m o n p a ∧ Inputs m o n ins) := rfl
@[grind =] theorem Reserved.nil : Reserved m o n [] = True := rfl
@[grind =] theorem Reserved.cons (p : BitVec 64) rsv :
    Reserved m o n (p :: rsv) = (ReservedAt m o n p ∧ Reserved m o n rsv) := rfl

variable {k : Nat} (hk : k < n) (hn : n < 2 ^ 61) (x : Int)
include hk hn

theorem InputAt.storeInt {p : BitVec 64} {a : Array (BitVec 64)} (h : InputAt m o n p a) :
    InputAt (Mem.storeInt m (cell o k) 8 x) o n p a where
  len := h.len
  words := by rw [words_storeInt_of_disjoint h.disj hk hn h.len]; exact h.words
  mapped := Mem.Mapped.storeInt h.mapped _ _ _
  disj := h.disj

theorem ReservedAt.storeInt {p : BitVec 64} (h : ReservedAt m o n p) :
    ReservedAt (Mem.storeInt m (cell o k) 8 x) o n p :=
  ⟨by rw [loadInt_storeInt_cell_of_disjoint h.disj hk hn]; exact h.loadInt_isSome, h.disj⟩

theorem Inputs.storeInt : ∀ {ins}, Inputs m o n ins → Inputs (Mem.storeInt m (cell o k) 8 x) o n ins
  | [], _ => trivial
  | (_, _) :: _, ⟨h, hs⟩ => ⟨h.storeInt hk hn x, Inputs.storeInt hs⟩

theorem Reserved.storeInt : ∀ {rsv}, Reserved m o n rsv →
    Reserved (Mem.storeInt m (cell o k) 8 x) o n rsv
  | [], _ => trivial
  | _ :: _, ⟨h, hs⟩ => ⟨h.storeInt hk hn x, Reserved.storeInt hs⟩

end

theorem ArrayLayout.storeInt_out {ins : List (BitVec 64 × Array (BitVec 64))} {o : BitVec 64}
    {n : Nat} {rsv : List (BitVec 64)} {m : DataMem} (h : ArrayLayout ins o n rsv m)
    {v : BitVec 64} (hv : v.toNat < n) (x : Int) :
    ArrayLayout ins o n rsv (Mem.storeInt m (o + v * 8#64) 8 x) := by
  rw [add_mul_eight]
  exact ⟨h.len, Mem.Mapped.storeInt h.mapped _ _ _, h.inputs.storeInt hv h.len x,
    h.reserved.storeInt hv h.len x⟩

grind_pattern ArrayLayout.storeInt_out =>
  Mem.storeInt m (o + v * 8#64) 8 x, ArrayLayout ins o n rsv m

/-! ## Steps -/

theorem wp_modify {σ : Type} (f : σ → σ) (Q : Unit → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩)
    (s : σ) : wp (modify f : BlockM σ Unit) Q E s = Q () (f s) := by
  rw [wp_BlockM_eq]
  rfl


section
variable {σa : Type} {view : DataMem → σa}
  {E : (CfgLabel → CfgLabel → DataMem → Prop) × EStack⟨⟩}

@[ascend] theorem wrp_load8_getElem {Q : BitVec 64 → BitVec 64 → DataMem → Prop}
    (p i : BitVec 64) (arr : Array (BitVec 64)) :
    (fun m => p ≐ₐ arr ∧ words m p arr.size = arr.toList ∧ Mem.Mapped [(p, 8 * arr.size)] m ∧
      i.toNat < arr.size ∧ arr.size < 2 ^ 61 ∧
      ∀ y, BitVec.ofInt 64 (Mem.loadInt m (p + i * 8#64) 8).get! ≐ y →
        Q (BitVec.ofInt 64 (Mem.loadInt m (p + i * 8#64) 8).get!) y m)
      ⊑ wrp (ofStateRepr view) (load8 (p + i * 8#64))
          (pure arr[i.toNat]! : BlockM σa (BitVec 64)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at hm
  obtain ⟨⟨-, hw, hmap, hi, hn, hk⟩, hq⟩ := hm
  have hval : BitVec.ofInt 64 (Mem.loadInt m (p + i * 8#64) 8).get! = arr[i.toNat]! := by
    rw [add_mul_eight, ← word, word_eq_getElem hw hi]
  rw [wp_load8, Concretization.post_pi]
  refine ⟨?_, arr[i.toNat]!, hk _ (PureRefinement.of_rel hval), ?_⟩
  · rw [add_mul_eight]
    exact Mem.Mapped.loadInt_isSome hmap (cell_inside hi hn)
  · simp only [ofStateRepr_pred]
    exact hq

@[ascend] theorem wrp_store8_set {Q : Unit → Unit → DataMem → Prop} (sp p i v v' : BitVec 64)
    (n : Nat) :
    (fun m => v ≐ v' ∧ i.toNat < n ∧ n < 2 ^ 61 ∧ Mem.Mapped [(p, 8 * n)] m ∧
      Mem.Blocks.Disjoint [(sp, 8)] [(p, 8 * n)] ∧
      Q () () (Mem.storeInt m (p + i * 8#64) 8 v.toInt))
      ⊑ wrp (ofStateRepr (outView p n)) (store8 sp (p + i * 8#64) v)
          (modify fun o => o.set! i.toNat v' : BlockM (Array (BitVec 64)) Unit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_modify] at hm
  obtain ⟨⟨hv, hi, hn, hmap, hd, hk⟩, hq⟩ := hm
  have hv : v = v' := hv trivial
  rw [wp_store8, Concretization.post_pi]
  rw [add_mul_eight] at hk ⊢
  refine ⟨⟨Mem.Mapped.loadInt_isSome hmap (cell_inside hi hn),
    Mem.Blocks.Disjoint.of_inside_right_pair hd (cell_inside hi hn)⟩, (), hk, ?_⟩
  simp only [ofStateRepr_pred]
  rw [outView_storeInt hi hn, hv]
  exact hq

@[ascend] theorem wrp_retAt_throw {CV AV : Type} {Q : CV → AV → DataMem → Prop} (sp : BitVec 64) :
    (fun m => (Mem.loadInt m sp 8).isSome = true ∧ E.1 .exit .exit m)
      ⊑ wrp (ofStateRepr view) (retAt sp : BlockM DataMem CV) (throw CfgLabel.exit : BlockM σa AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_throw_block] at hm
  obtain ⟨⟨hl, he⟩, hw⟩ := hm
  rw [wp_retAt]
  refine ⟨hl, ?_⟩
  simp only [EPostsConcretization.ePosts_cons]
  rw [Concretization.post_pi]
  exact ⟨.exit, he, hw⟩

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

end Array

