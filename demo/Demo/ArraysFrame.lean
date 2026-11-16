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

theorem wrp_assert_dmemOk {β AV : Type} {view : FState → σa} {x : BlockM FState β}
    {a : BlockM σa AV} {Q : β → AV → FState → Prop} (p : BitVec 64) (n : Nat) {pre : FState → Prop}
    (h : pre ⊑ wrp (ofStateRepr view) x a Q E) :
    (fun s => Mem.Blocks.Disjoint [(p, n)] bs ∧ pre s)
      ⊑ wrp (ofStateRepr view) (do StateT.assert fun (_ : FState) => DmemOk bs p n .dmem; x : BlockM FState β) a Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at hs
  obtain ⟨⟨hd, hp⟩, ha⟩ := hs
  rw [wp_assert_bind]
  exact ⟨hd, wrp_transport h Qa Ea s
    (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ⟨hp, ha⟩)⟩

theorem disjoint_cell {w n j : Nat} {p : BitVec 64} (hd : Mem.Blocks.Disjoint [(p, w * n)] bs)
    (hw : w ≤ 8) (hj : j < n) (hn : n < 2 ^ 61) : Mem.Blocks.Disjoint [(cell w p j, w)] bs :=
  fun c hc => hd c (hc.of_singleton (cell_inside hw hj hn))

@[ascend] theorem wrp_loadIn_getElem {view : DataMem → σa} {Q : BitVec 64 → BitVec 64 → FState → Prop}
    (w b : Nat) (p o : BitVec 64) (arr : Array (BitVec b)) (j : Nat) (P : Prop) (harr : p ≐ₐ arr)
    (hij : PureRefinement o j P (Scaled w)) :
    (fun s => P ∧ w ≤ 8 ∧ b = 8 * w ∧
      words w b s.dmem p arr.size = arr.toList ∧ Mem.Mapped [(p, w * arr.size)] s.dmem ∧ j < arr.size ∧
      arr.size < 2 ^ 61 ∧ Mem.Blocks.Disjoint [(p, w * arr.size)] bs ∧
      ∀ y, BitVec.ofInt 64 ((Mem.loadInt s.dmem (p + o) w).get! % 2 ^ (8 * w)) ≐ y →
        Q (BitVec.ofInt 64 ((Mem.loadInt s.dmem (p + o) w).get! % 2 ^ (8 * w))) y s)
      ⊑ wrp (ofStateRepr fun s : FState => view s.dmem) (loadIn bs .dmem w (p + o))
          (pure ((arr[j]!).setWidth 64) : BlockM σa (BitVec 64)) Q E := by
  have h := wrp_assert_dmemOk (bs := bs) (E := E) (p + o) w (wrp_zoom_dmem _ fun s =>
    wrp_load_getElem (view := view) (Q := fun v y m => Q v y (s.set .dmem m))
      (E := (fun l l' m => E.1 l l' (s.set .dmem m), estack⟨⟩)) w b p o arr j P harr hij)
  refine PartialOrder.rel_trans ?_ h
  intro s ⟨hP, hw, hb, hwd, hmap, hj, hn, hd, hk⟩
  have hcell : p + o = cell w p j := by rw [hij hP]; rfl
  exact ⟨hcell ▸ disjoint_cell hd hw hj hn, hP, hw, hb, hwd, hmap, hj, hn,
    fun y hy => by rw [FState.set_dmem_self]; exact hk y hy⟩

@[ascend] theorem wrp_storeIn_set {Q : Unit → Unit → FState → Prop} (w b : Nat) (p o v v' : BitVec 64)
    (n j : Nat) (P : Prop) (hij : PureRefinement o j P (Scaled w)) :
    (fun s => v ≐ v' ∧ P ∧ w ≤ 8 ∧ b = 8 * w ∧ j < n ∧ n < 2 ^ 61 ∧
      Mem.Mapped [(p, w * n)] s.dmem ∧ Mem.Blocks.Disjoint [(p, w * n)] bs ∧
      Q () () (s.set .dmem (Mem.storeInt s.dmem (cell w p j) w v.toInt)))
      ⊑ wrp (ofStateRepr fun s : FState => outView w b p n s.dmem) (storeIn bs .dmem w (p + o) v)
          (modify fun o => o.set! j (v'.setWidth b) : BlockM (Array (BitVec b)) Unit) Q E := by
  have h := wrp_assert_dmemOk (bs := bs) (E := E) (p + o) w (wrp_zoom_dmem _ fun s =>
    wrp_store_set (Q := fun u u' m => Q u u' (s.set .dmem m))
      (E := (fun l l' m => E.1 l l' (s.set .dmem m), estack⟨⟩)) w b p o v v' n j P hij)
  refine PartialOrder.rel_trans ?_ h
  intro s ⟨hv, hP, hw, hb, hj, hn, hmap, hd, hk⟩
  have hcell : p + o = cell w p j := by rw [hij hP]; rfl
  exact ⟨hcell ▸ disjoint_cell hd hw hj hn, hv, hP, hw, hb, hj, hn, hmap, hk⟩

@[ascend default - 1] theorem wrp_loadIn_get_at {Q : BitVec 64 → BitVec 64 → FState → Prop} (w b : Nat) (p c : BitVec 64)
    (n j : Nat) (P : Prop) (hij : PureRefinement c j P (Index w p)) :
    (fun s => P ∧ w ≤ 8 ∧ b = 8 * w ∧ j < n ∧ n < 2 ^ 61 ∧
      Mem.Mapped [(p, w * n)] s.dmem ∧ Mem.Blocks.Disjoint [(p, w * n)] bs ∧
      ∀ y, BitVec.ofInt 64 ((Mem.loadInt s.dmem c w).get! % 2 ^ (8 * w)) ≐ y →
        Q (BitVec.ofInt 64 ((Mem.loadInt s.dmem c w).get! % 2 ^ (8 * w))) y s)
      ⊑ wrp (ofStateRepr fun s : FState => outView w b p n s.dmem) (loadIn bs .dmem w c)
          (get >>= fun arr : Array (BitVec b) => pure ((arr[j]!).setWidth 64) : BlockM (Array (BitVec b)) (BitVec 64))
          Q E := by
  have h := wrp_assert_dmemOk (bs := bs) (E := E) c w (wrp_zoom_dmem _ fun s =>
    wrp_load_get (Q := fun v y m => Q v y (s.set .dmem m))
      (E := (fun l l' m => E.1 l l' (s.set .dmem m), estack⟨⟩)) w b p c n j P hij)
  refine PartialOrder.rel_trans ?_ h
  intro s ⟨hP, hw, hb, hj, hn, hmap, hd, hk⟩
  have hcell : c = cell w p j := hij hP
  exact ⟨hcell ▸ disjoint_cell hd hw hj hn, hP, hw, hb, hj, hn, hmap,
    fun y hy => by rw [FState.set_dmem_self]; exact hk y hy⟩

@[ascend default - 1] theorem wrp_storeIn_set_at {Q : Unit → Unit → FState → Prop} (w b : Nat) (p c v v' : BitVec 64)
    (n j : Nat) (P : Prop) (hij : PureRefinement c j P (Index w p)) :
    (fun s => v ≐ v' ∧ P ∧ w ≤ 8 ∧ b = 8 * w ∧ j < n ∧ n < 2 ^ 61 ∧
      Mem.Mapped [(p, w * n)] s.dmem ∧ Mem.Blocks.Disjoint [(p, w * n)] bs ∧
      Q () () (s.set .dmem (Mem.storeInt s.dmem (cell w p j) w v.toInt)))
      ⊑ wrp (ofStateRepr fun s : FState => outView w b p n s.dmem) (storeIn bs .dmem w c v)
          (modify fun o => o.set! j (v'.setWidth b) : BlockM (Array (BitVec b)) Unit) Q E := by
  have h := wrp_assert_dmemOk (bs := bs) (E := E) c w (wrp_zoom_dmem _ fun s =>
    wrp_store_set_at (Q := fun u u' m => Q u u' (s.set .dmem m))
      (E := (fun l l' m => E.1 l l' (s.set .dmem m), estack⟨⟩)) w b p c v v' n j P hij)
  refine PartialOrder.rel_trans ?_ h
  intro s ⟨hv, hP, hw, hb, hj, hn, hmap, hd, hk⟩
  have hcell : c = cell w p j := hij hP
  exact ⟨hcell ▸ disjoint_cell hd hw hj hn, hv, hP, hw, hb, hj, hn, hmap, hk⟩

/-! ## The frame under a view of `dmem`

An access to the frame leaves `dmem` unchanged, so it refines a `pure` step. -/

@[ascend] theorem wrp_zoom_frame_store {view : DataMem → σa} {Q : Unit → Unit → FState → Prop} (n : Nat)
    (a v : BitVec 64) :
    (fun s => (Mem.loadInt s.frame a n).isSome = true ∧
      Q () () (s.set .frame (Mem.storeInt s.frame a n v.toInt)))
      ⊑ wrp (ofStateRepr fun s : FState => view s.dmem) (zoom .frame (store n a v))
          (pure () : BlockM σa Unit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at hs
  obtain ⟨⟨hm, hq⟩, hqa⟩ := hs
  rw [wp_zoom, wp_store, Concretization.post_pi]
  exact ⟨hm, (), hq, hqa⟩

@[ascend] theorem wrp_zoom_frame_load {view : DataMem → σa} {Q : BitVec 64 → BitVec 64 → FState → Prop}
    (n : Nat) (a : BitVec 64) :
    (fun s => (Mem.loadInt s.frame a n).isSome = true ∧
      Q (BitVec.ofInt 64 ((Mem.loadInt s.frame a n).get! % 2 ^ (8 * n))) 0#64 s)
      ⊑ wrp (ofStateRepr fun s : FState => view s.dmem) (zoom .frame (load n a))
          (pure 0#64 : BlockM σa (BitVec 64)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at hs
  obtain ⟨⟨hm, hq⟩, hqa⟩ := hs
  rw [wp_zoom, wp_load, FState.set_get, Concretization.post_pi]
  exact ⟨hm, 0#64, hq, hqa⟩

grind_pattern Mem.Mapped.loadInt_isSome => Mem.Mapped bs m, Mem.loadInt m addr n
grind_pattern Mem.Mapped.storeInt => Mem.Mapped bs (Mem.storeInt m a n v)

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

theorem Mapped.split_frame (h : Mem.Mapped bs m) : Mem.Mapped bs (FState.split bs m).frame := fun b hb => by
  rw [get?_split_frame, if_pos hb]
  exact h b hb

theorem outView_split_eq_words {p : BitVec 64} {n : Nat} (hd : Mem.Blocks.Disjoint [(p, 8 * n)] bs)
    (hn : n < 2 ^ 61) : outView 8 64 p n (FState.split bs m).dmem = (words 8 64 m p n).toArray := by
  rw [outView_split hd (Nat.le_refl 8) hn]
  rfl

grind_pattern outView_split_eq_words => outView 8 64 p n (FState.split bs m).dmem

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

/-- The concretization from the machine memory to the array of `n` words at `O`, through the frame
of `k` words at `r₀`. -/
noncomputable abbrev memToArray (r₀ O : BitVec 64) (k n : Nat) :=
  ((ofStateRepr MachineData.dmem).comp ((ofStateRepr (FState.split (Fr r₀ k 0))).comp
    (ofStateRepr fun s : FState => outView 8 64 O n s.dmem))).comp (purify (Array (BitVec 64)))

/-- `memToArray` from the abstract machine state. -/
noncomputable abbrev machineToArray (r₀ O : BitVec 64) (k n : Nat) :=
  (ofStateRepr abs).comp (memToArray r₀ O k n)

end Ascent.Kraken
