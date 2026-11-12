import Demo.Lift

/-!
# The stack frame

A program over the data memory refines a program over a state `FState` with two memories: the
cells of the stack frame of the running function, and the data memory outside the frame. The
concretization `ofStateRepr (FState.split bs)` splits the memory at the blocks `bs` of the frame:
`frame` holds the cells inside `bs`, and `dmem` holds all other cells.

For a function with the stack pointer `r₀` at entry, `k` reserved words below the return slot and
`n` words of stack arguments above it, the frame is the single block `Fr r₀ k n` from `r₀ - 8k` to
`r₀ + 8 + 8n`. It holds the reserved words, the return slot at `r₀` and the stack arguments.

The abstract program accesses one of the two memories with `zoom`. An address computed from the
stack pointer goes to `frame` with the verification condition that the access lies inside `bs`, and
every other address goes to `dmem` with the condition that the access is apart from `bs`. The
hypothesis `rsp ≐ₛ x` marks the value `rsp` as a stack address, and the `@[ascend_pure]` rules of
`StackAddr` propagate the mark through offsets.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Kraken

/-! ## States -/

inductive Region where
  | dmem
  | frame

@[ext] structure FState where
  dmem : DataMem
  frame : DataMem

namespace FState

def get : FState → Region → DataMem
  | s, .dmem => s.dmem
  | s, .frame => s.frame

def set : FState → Region → DataMem → FState
  | s, .dmem, m => { s with dmem := m }
  | s, .frame, m => { s with frame := m }

def split (bs : List (BitVec 64 × Nat)) (m : DataMem) : FState :=
  ⟨m.filter fun b _ => !decide (Mem.Blocks.Inside b 1 bs), m.restrict bs⟩

end FState

/-- The frame of a function with the stack pointer `r₀` at entry: `k` reserved words, the return
slot and `n` words of stack arguments. -/
def Fr (r₀ : BitVec 64) (k n : Nat) : List (BitVec 64 × Nat) :=
  [(r₀ - BitVec.ofNat 64 (8 * k), 8 * k + 8 + 8 * n)]

@[grind =] theorem inside_Fr {a r₀ : BitVec 64} {n k j : Nat} :
    Mem.Blocks.Inside a n (Fr r₀ k j)
      = ((a - (r₀ - BitVec.ofNat 64 (8 * k))).toNat + n ≤ 8 * k + 8 + 8 * j) := by
  simp only [Fr, Mem.Blocks.Inside, or_false]

theorem loadInt_storeInt_of_sub {m : DataMem} {a x : BitVec 64} {n k : Nat} (v : Int)
    (h₁ : n ≤ (x - a).toNat) (h₂ : k ≤ (a - x).toNat) :
    (m.storeInt a n v).loadInt x k = m.loadInt x k :=
  Mem.loadInt_storeInt_of_disjoint (Mem.Blocks.Disjoint.of_sub h₁ h₂) v

grind_pattern loadInt_storeInt_of_sub => (Mem.storeInt m a n v).loadInt x k

/-! ## The split -/

section
variable {bs : List (BitVec 64 × Nat)} {m : DataMem}

theorem get?_split_frame (b : BitVec 64) :
    (FState.split bs m).frame.get? b = if Mem.Blocks.Inside b 1 bs then m.get? b else none :=
  Mem.get?_restrict m bs b

theorem get?_split_dmem (b : BitVec 64) :
    (FState.split bs m).dmem.get? b = if Mem.Blocks.Inside b 1 bs then none else m.get? b := by
  simp only [FState.split, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_filter']
  by_cases h : Mem.Blocks.Inside b 1 bs <;> cases m[b]? <;> simp [h, Option.filter]

/-- The access of `n` bytes at `a` lies in the region `r`. -/
def InRegion (bs : List (BitVec 64 × Nat)) (a : BitVec 64) (n : Nat) : Region → Prop
  | .frame => Mem.Blocks.Inside a n bs
  | .dmem => Mem.Blocks.Disjoint [(a, n)] bs

theorem InRegion.get? {a : BitVec 64} {n : Nat} {r : Region} (h : InRegion bs a n r) {i : Nat}
    (hi : i < n) : ((FState.split bs m).get r).get? (a + BitVec.ofNat 64 i) = m.get? (a + BitVec.ofNat 64 i) := by
  cases r
  · have hd : ¬ Mem.Blocks.Inside (a + BitVec.ofNat 64 i) 1 bs :=
      h _ ((Mem.Blocks.Inside.base (Nat.le_refl n)).add_ofNat hi)
    simp only [FState.get, get?_split_dmem, hd, ite_false]
  · simp only [FState.get, get?_split_frame, h.add_ofNat hi, ite_true]

theorem InRegion.loadInt {a : BitVec 64} {n : Nat} {r : Region} (h : InRegion bs a n r) :
    Mem.loadInt ((FState.split bs m).get r) a n = Mem.loadInt m a n :=
  Mem.loadInt_congr fun _ hi => h.get? hi

theorem InRegion.split_storeInt {a : BitVec 64} {n : Nat} {r : Region} (h : InRegion bs a n r)
    (v : Int) :
    FState.split bs (Mem.storeInt m a n v)
      = (FState.split bs m).set r (Mem.storeInt ((FState.split bs m).get r) a n v) := by
  have hin : ∀ b, b ∈ (Int.toBytes n v).At a → Mem.Blocks.Inside b 1 [(a, n)] := fun b hb => by
    rw [mem_At_iff, Int.toBytes_length] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact (Mem.Blocks.Inside.base (Nat.le_refl n)).add_ofNat hi
  cases r
  · have hd : ∀ b, b ∈ (Int.toBytes n v).At a → ¬ Mem.Blocks.Inside b 1 bs := fun b hb => h b (hin b hb)
    simp only [FState.set, FState.get]
    apply FState.ext <;> apply Std.ExtHashMap.ext_getElem? <;> intro b <;>
      simp only [← Std.ExtHashMap.get?_eq_getElem?, get?_split_dmem, get?_split_frame, Mem.get?_storeInt]
    · by_cases hb : b ∈ (Int.toBytes n v).At a
      · simp [hd b hb]
      · rw [Std.ExtHashMap.get?_eq_getElem? (a := b), Std.ExtHashMap.getElem?_eq_none hb]
        simp
    · by_cases hb : b ∈ (Int.toBytes n v).At a
      · simp [hd b hb]
      · rw [Std.ExtHashMap.get?_eq_getElem? (a := b), Std.ExtHashMap.getElem?_eq_none hb]
        simp
  · have hf : ∀ b, b ∈ (Int.toBytes n v).At a → Mem.Blocks.Inside b 1 bs := fun b hb => by
      obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hb
      rw [Int.toBytes_length] at hi
      exact h.add_ofNat hi
    simp only [FState.set, FState.get]
    apply FState.ext <;> apply Std.ExtHashMap.ext_getElem? <;> intro b <;>
      simp only [← Std.ExtHashMap.get?_eq_getElem?, get?_split_dmem, get?_split_frame, Mem.get?_storeInt]
    · by_cases hb : b ∈ (Int.toBytes n v).At a
      · simp [hf b hb]
      · rw [Std.ExtHashMap.get?_eq_getElem? (a := b), Std.ExtHashMap.getElem?_eq_none hb]
        simp
    · by_cases hb : b ∈ (Int.toBytes n v).At a
      · simp [hf b hb]
      · rw [Std.ExtHashMap.get?_eq_getElem? (a := b), Std.ExtHashMap.getElem?_eq_none hb]
        simp

end

/-! ## Programs over one region -/

/-- Run the program `x` over the data memory on the region `r` of the state. -/
def zoom {α : Type} (r : Region) (x : BlockM DataMem α) : BlockM FState α :=
  ExceptT.mk fun s => (fun p => (p.1, s.set r p.2)) <$> x.run.run (s.get r)

theorem wp_zoom {α : Type} (r : Region) (x : BlockM DataMem α) (Q : α → FState → Prop)
    (E : (Int64 → FState → Prop) × EStack⟨⟩) (s : FState) :
    wp (zoom r x) Q E s
      = wp x (fun v m => Q v (s.set r m)) (fun l m => E.1 l (s.set r m), estack⟨⟩) (s.get r) := by
  rw [wp_BlockM_eq, wp_BlockM_eq, show (zoom r x).run.run s
    = ((fun p => (p.1, s.set r p.2)) <$> x.run.run (s.get r) : Option _) from rfl]
  rcases x.run.run (s.get r) with _ | ⟨_ | _, _⟩ <;> rfl

/-! ## Addresses -/

/-- The value is an address computed from the stack pointer. -/
def StackAddr (a x : BitVec 64) : Prop := a = x

/-- `a ≐ₛ x`: the concrete stack address `a` is the abstract value `x`. -/
scoped notation:50 c:51 " ≐ₛ " x:51 => PureRefinement c x True StackAddr

/-- The access of `n` bytes at the concrete address `a` goes to the region `p.1` at the abstract
address `p.2`. -/
def Located (bs : List (BitVec 64 × Nat)) (n : Nat) (a : BitVec 64) (p : Region × BitVec 64) : Prop :=
  a = p.2 ∧ InRegion bs a n p.1

section
variable {a b x y : BitVec 64} {P₁ P₂ : Prop} {bs : List (BitVec 64 × Nat)} {n : Nat}

@[ascend_pure] theorem stack_add (h₁ : PureRefinement a x P₁ StackAddr) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂) StackAddr := fun ⟨hp₁, hp₂⟩ => by
  rw [StackAddr, h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem stack_sub (h₁ : PureRefinement a x P₁ StackAddr) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a - b) (x - y) (P₁ ∧ P₂) StackAddr := fun ⟨hp₁, hp₂⟩ => by
  rw [StackAddr, h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_stackAddr (h : PureRefinement a x P₁ StackAddr) :
    PureRefinement a x P₁ Eq :=
  h

@[ascend_pure] theorem loc_frame (h : PureRefinement a x P₁ StackAddr) :
    PureRefinement a (Region.frame, x) (P₁ ∧ Mem.Blocks.Inside a n bs) (Located bs n) :=
  fun ⟨hp, hi⟩ => ⟨h hp, hi⟩

@[ascend_pure low] theorem loc_dmem (h : PureRefinement a x P₁ Eq) :
    PureRefinement a (Region.dmem, x) (P₁ ∧ Mem.Blocks.Disjoint [(a, n)] bs) (Located bs n) :=
  fun ⟨hp, hd⟩ => ⟨h hp, hd⟩

end

/-! ## Steps -/

section
variable {bs : List (BitVec 64 × Nat)} {E : (Int64 → Int64 → DataMem → Prop) × EStack⟨⟩}

@[ascend] theorem wrp_load_zoom {Q : BitVec 64 → BitVec 64 → DataMem → Prop} (n : Nat)
    (a : BitVec 64) (r : Region) (x : BitVec 64) (P : Prop) :
    (fun m => PureRefinement a (r, x) P (Located bs n) ∧ P ∧
      ∀ y, BitVec.ofInt 64 ((Mem.loadInt m a n).get! % 2 ^ (8 * n)) ≐ y →
        Q (BitVec.ofInt 64 ((Mem.loadInt m a n).get! % 2 ^ (8 * n))) y m)
      ⊑ wrp (ofStateRepr (FState.split bs)) (load n a) (zoom r (load n x)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_zoom, wp_load] at hm
  obtain ⟨⟨hl, hP, hq⟩, hs, hqa⟩ := hm
  obtain ⟨rfl, hr⟩ := hl hP
  rw [hr.loadInt] at hs hqa
  rw [wp_load, Concretization.post_pi]
  refine ⟨hs, _, hq _ (PureRefinement.of_rel rfl), ?_⟩
  simp only [ofStateRepr_pred]
  cases r <;> exact hqa

@[ascend] theorem wrp_store_zoom {Q : Unit → Unit → DataMem → Prop} (n : Nat) (a v : BitVec 64)
    (r : Region) (x v' : BitVec 64) (P : Prop) :
    (fun m => PureRefinement a (r, x) P (Located bs n) ∧ v ≐ v' ∧ P ∧
      Q () () (Mem.storeInt m a n v.toInt))
      ⊑ wrp (ofStateRepr (FState.split bs)) (store n a v) (zoom r (store n x v')) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_zoom, wp_store] at hm
  obtain ⟨⟨hl, hv, hP, hq⟩, hs, hqa⟩ := hm
  obtain ⟨rfl, hr⟩ := hl hP
  have hv : v = v' := hv trivial
  subst hv
  rw [hr.loadInt] at hs
  rw [wp_store, Concretization.post_pi]
  refine ⟨hs, (), hq, ?_⟩
  simp only [ofStateRepr_pred, hr.split_storeInt]
  exact hqa

end

end Ascent.Kraken
