import Demo.Arrays
import Demo.Frame

/-!
# Arrays in the data memory of a split state

The rules of `Demo.Arrays` for a program over `FState`. The concretization reads the array from
`dmem` alone. A load or a store of `loadIn bs .dmem` and `storeIn bs .dmem` assumes that the access
misses the frame `bs`; the rules discharge that assumption from the layout fact that the whole
array misses the frame.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Kraken

section
variable {σa : Type} {bs : List (BitVec 64 × Nat)} {E : (Int64 → Int64 → FState → Prop) × EStack⟨⟩}

theorem wrp_assume_dmemOk {β AV : Type} {view : FState → σa} {x : BlockM FState β}
    {a : BlockM σa AV} {Q : β → AV → FState → Prop} (p : BitVec 64) (n : Nat) {pre : FState → Prop}
    (h : pre ⊑ wrp (ofStateRepr view) x a Q E) :
    (fun s => Mem.Blocks.Disjoint [(p, n)] bs ∧ pre s)
      ⊑ wrp (ofStateRepr view) (do StateT.assume fun (_ : FState) => DmemOk bs p n .dmem; x : BlockM FState β) a Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at hs
  obtain ⟨⟨hd, hp⟩, ha⟩ := hs
  rw [wp_assume_bind]
  exact ⟨hd, wrp_transport h Qa Ea s
    (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ⟨hp, ha⟩)⟩

theorem disjoint_cell {w n j : Nat} {p : BitVec 64} (hd : Mem.Blocks.Disjoint [(p, w * n)] bs)
    (hw : w ≤ 8) (hj : j < n) (hn : n < 2 ^ 61) : Mem.Blocks.Disjoint [(cell w p j, w)] bs :=
  fun c hc => hd c (hc.of_singleton (cell_inside hw hj hn))

@[ascend] theorem wrp_loadIn_getElem {view : DataMem → σa} {Q : BitVec 64 → BitVec 64 → FState → Prop}
    (w b : Nat) (p o : BitVec 64) (arr : Array (BitVec b)) (j : Nat) (P : Prop) :
    (fun s => p ≐ₐ arr ∧ PureRefinement o j P (Scaled w) ∧ P ∧ w ≤ 8 ∧ b = 8 * w ∧
      words w b s.dmem p arr.size = arr.toList ∧ Mem.Mapped [(p, w * arr.size)] s.dmem ∧ j < arr.size ∧
      arr.size < 2 ^ 61 ∧ Mem.Blocks.Disjoint [(p, w * arr.size)] bs ∧
      ∀ y, BitVec.ofInt 64 ((Mem.loadInt s.dmem (p + o) w).get! % 2 ^ (8 * w)) ≐ y →
        Q (BitVec.ofInt 64 ((Mem.loadInt s.dmem (p + o) w).get! % 2 ^ (8 * w))) y s)
      ⊑ wrp (ofStateRepr fun s : FState => view s.dmem) (loadIn bs .dmem w (p + o))
          (pure ((arr[j]!).setWidth 64) : BlockM σa (BitVec 64)) Q E := by
  have h := wrp_assume_dmemOk (bs := bs) (E := E) (p + o) w (wrp_zoom_dmem _ fun s =>
    wrp_load_getElem (view := view) (Q := fun v y m => Q v y (s.set .dmem m))
      (E := (fun l l' m => E.1 l l' (s.set .dmem m), estack⟨⟩)) w b p o arr j P)
  refine PartialOrder.rel_trans ?_ h
  intro s ⟨hpa, hij, hP, hw, hb, hwd, hmap, hj, hn, hd, hk⟩
  have hcell : p + o = cell w p j := by rw [hij hP]; rfl
  exact ⟨hcell ▸ disjoint_cell hd hw hj hn, hpa, hij, hP, hw, hb, hwd, hmap, hj, hn,
    fun y hy => by rw [FState.set_dmem_self]; exact hk y hy⟩

@[ascend] theorem wrp_storeIn_set {Q : Unit → Unit → FState → Prop} (w b : Nat) (p o v v' : BitVec 64)
    (n j : Nat) (P : Prop) :
    (fun s => v ≐ v' ∧ PureRefinement o j P (Scaled w) ∧ P ∧ w ≤ 8 ∧ b = 8 * w ∧ j < n ∧ n < 2 ^ 61 ∧
      Mem.Mapped [(p, w * n)] s.dmem ∧ Mem.Blocks.Disjoint [(p, w * n)] bs ∧
      Q () () (s.set .dmem (Mem.storeInt s.dmem (cell w p j) w v.toInt)))
      ⊑ wrp (ofStateRepr fun s : FState => outView w b p n s.dmem) (storeIn bs .dmem w (p + o) v)
          (modify fun o => o.set! j (v'.setWidth b) : BlockM (Array (BitVec b)) Unit) Q E := by
  have h := wrp_assume_dmemOk (bs := bs) (E := E) (p + o) w (wrp_zoom_dmem _ fun s =>
    wrp_store_set (Q := fun u u' m => Q u u' (s.set .dmem m))
      (E := (fun l l' m => E.1 l l' (s.set .dmem m), estack⟨⟩)) w b p o v v' n j P)
  refine PartialOrder.rel_trans ?_ h
  intro s ⟨hv, hij, hP, hw, hb, hj, hn, hmap, hd, hk⟩
  have hcell : p + o = cell w p j := by rw [hij hP]; rfl
  exact ⟨hcell ▸ disjoint_cell hd hw hj hn, hv, hij, hP, hw, hb, hj, hn, hmap, hk⟩

end

/-! ## Layouts in the split state -/

section
variable {bs : List (BitVec 64 × Nat)} {m : DataMem} {w b n : Nat} {p : BitVec 64}

theorem loadInt_split_dmem {a : BitVec 64} {k : Nat} (hd : Mem.Blocks.Disjoint [(a, k)] bs) :
    Mem.loadInt (FState.split bs m).dmem a k = Mem.loadInt m a k :=
  InRegion.loadInt (r := .dmem) hd

theorem words_split (hd : Mem.Blocks.Disjoint [(p, w * n)] bs) (hw : w ≤ 8) (hn : n < 2 ^ 61) :
    words w b (FState.split bs m).dmem p n = words w b m p n := by
  apply List.ext_getElem
  · simp [words]
  intro j h₁ _
  simp only [words, List.length_ofFn] at h₁
  simp only [words, List.getElem_ofFn, word]
  rw [loadInt_split_dmem (disjoint_cell hd hw h₁ hn)]

theorem outView_split (hd : Mem.Blocks.Disjoint [(p, w * n)] bs) (hw : w ≤ 8) (hn : n < 2 ^ 61) :
    outView w b p n (FState.split bs m).dmem = outView w b p n m := by
  rw [outView, outView, words_split hd hw hn]

theorem Mapped.split {k : Nat} (h : Mem.Mapped [(p, k)] m) (hd : Mem.Blocks.Disjoint [(p, k)] bs) :
    Mem.Mapped [(p, k)] (FState.split bs m).dmem := fun c hc => by
  rw [get?_split_dmem, if_neg (hd c hc)]
  exact h c hc

theorem InputAt.split {o q : BitVec 64} {a : Array (BitVec b)} (h : InputAt w b m o n q a)
    (hw : w ≤ 8) (hd : Mem.Blocks.Disjoint [(q, w * a.size)] bs) :
    InputAt w b (FState.split bs m).dmem o n q a where
  len := h.len
  words := by rw [words_split hd hw h.len]; exact h.words
  mapped := Mapped.split h.mapped hd
  disj := h.disj

end

end Ascent.Kraken
