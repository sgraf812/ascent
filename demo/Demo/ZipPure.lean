import Demo.ZipArr

/-!
# What `zipWithAdd` computes, from the array program

`wp_zipWithAddArr` states the result of the synthesized array program `zipWithAddArr`: it exits
with the output array `Array.zipWith (· + ·) a b`. `wp_zipWithAddL` carries this result to the
lifted program through `zipWithAddArr.refines`, and `zipWithAdd_correct` carries it back to the
x64 text through the refinements of `zipWithAddL`, `zipWithAddT` and the first layer.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)
open scoped Program.WP

namespace Ascent.Kraken

/-- The memory at the entry of `zipWithAdd`: arrays `A`, `B` and `O` of `n` mapped words, the output
array apart from the inputs and from the return slot at `rsp`, and the return slot mapped. -/
structure ZipArrays (m : DataMem) (A B O rsp : BitVec 64) (n : Nat) : Prop where
  len : n < 2 ^ 61
  mapA : Mem.Mapped [(A, 8 * n)] m
  mapB : Mem.Mapped [(B, 8 * n)] m
  mapO : Mem.Mapped [(O, 8 * n)] m
  disjA : Mem.Blocks.Disjoint [(O, 8 * n)] [(A, 8 * n)]
  disjB : Mem.Blocks.Disjoint [(O, 8 * n)] [(B, 8 * n)]
  disjR : Mem.Blocks.Disjoint [(rsp, 8)] [(O, 8 * n)]
  ret : (Mem.loadInt m rsp 8).isSome = true

theorem ZipArrays.layout {m : DataMem} {A B O rsp : BitVec 64} {n : Nat}
    (h : ZipArrays m A B O rsp n) :
    ZipLayout A B O rsp n (words m A n).toArray (words m B n).toArray m where
  len := h.len
  sizeA := by simp [words]
  sizeB := by simp [words]
  wordsA := by simp [words]
  wordsB := by simp [words]
  mapA := h.mapA
  mapB := h.mapB
  mapO := h.mapO
  disjA := h.disjA
  disjB := h.disjB
  disjR := h.disjR
  ret := h.ret

theorem eq_zipWith_of_getElem! {o a b : Array (BitVec 64)} {n : Nat} (ho : o.size = n)
    (ha : a.size = n) (hb : b.size = n) (h : ∀ i < n, o[i]! = a[i]! + b[i]!) :
    o = Array.zipWith (· + ·) a b := by
  apply Array.ext
  · simp [ho, ha, hb]
  · intro i h₁ _
    rw [Array.getElem_zipWith]
    have hi := h i (ho ▸ h₁)
    rwa [getElem!_pos o i h₁, getElem!_pos a i (by omega), getElem!_pos b i (by omega)] at hi

theorem wp_zipWithAddArr [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)
    (A B O rsp : BitVec 64) {n : Nat} {a b o : Array (BitVec 64)} (hn : n < 2 ^ 61)
    (ha : a.size = n) (hb : b.size = n) (ho : o.size = n) :
    wp (zipWithAddArr s ra A B O rsp n a b) (fun _ _ => False)
      (fun (l : CfgLabel) (o' : Array (BitVec 64)) => l = CfgLabel.exit ∧ o' = Array.zipWith (· + ·) a b, estack⟨⟩) o := by
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  have h1 : (1#64 : BitVec 64) = 1 := rfl
  unfold zipWithAddArr
  simp only [h0, h1]
  by_cases hn0 : n = 0
  · subst hn0
    simp only [cmp_le_self_zero, ↓reduceIte, wp_throw_block]
    exact ⟨trivial, eq_zipWith_of_getElem! ho ha hb fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  simp only [cmp_le_self_of_pos (Nat.pos_of_ne_zero hn0) hn, Bool.false_eq_true, ↓reduceIte,
    WPMonadExact.wp_bind_eq]
  suffices hloop : ∀ j k (o : Array (BitVec 64)), n - k = j → k < n → o.size = n →
      (∀ i < k, o[i]! = a[i]! + b[i]!) →
      wp (FixLoop.mk.forIn (BitVec.ofNat 64 k) fun _ (v : BitVec 64) => do
        let x ← (pure b[v.toNat]! : BlockM (Array (BitVec 64)) (BitVec 64))
        let x_1 ← (pure a[v.toNat]! : BlockM (Array (BitVec 64)) (BitVec 64))
        modify fun (o : Array (BitVec 64)) => o.set! v.toNat (x_1 + x)
        if CondCode.cmp .nz (BitVec.ofNat 64 n) (v + 1) = true then pure (ForInStep.yield (v + 1))
          else do
            throw CfgLabel.exit
            pure (ForInStep.done (v + 1)))
        (fun _ => wp (pure PUnit.unit : BlockM (Array (BitVec 64)) Unit) (fun _ _ => False)
          (fun (l : CfgLabel) (o' : Array (BitVec 64)) => l = CfgLabel.exit ∧ o' = Array.zipWith (· + ·) a b, estack⟨⟩))
        (fun (l : CfgLabel) (o' : Array (BitVec 64)) => l = CfgLabel.exit ∧ o' = Array.zipWith (· + ·) a b, estack⟨⟩) o by
    exact hloop n 0 o (Nat.sub_zero n) (Nat.pos_of_ne_zero hn0) ho fun i hi => absurd hi (Nat.not_lt_zero i)
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro k o hj hk ho hpre
    rw [FixLoop.forIn_eq]
    simp only [WPMonadExact.wp_bind_eq, WPMonadExact.wp_pure_eq, wp_modify,
      toNat_ofNat_lt (show k < 2 ^ 61 by omega)]
    rw [cmp_nz_succ hk hn]
    have hset : ∀ i < k + 1, (o.set! k (a[k]! + b[k]!))[i]! = a[i]! + b[i]! := by
      intro i hi
      have hio : i < o.size := by omega
      have hs : (o.set! k (a[k]! + b[k]!))[i]! = if k = i then a[k]! + b[k]! else o[i]! := by
        simp [Array.set!_eq_setIfInBounds, getElem!_pos, hio, Array.getElem_setIfInBounds]
      rw [hs]
      by_cases hki : k = i
      · simp only [hki, ↓reduceIte]
      · simp only [hki, ↓reduceIte]
        exact hpre i (by omega)
    by_cases hkn : k + 1 = n
    · simp only [hkn, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        WPMonadExact.wp_bind_eq, wp_throw_block]
      refine ⟨trivial, eq_zipWith_of_getElem! (by simp [ho]) ha hb fun i hi => hset i (by omega)⟩
    · simp only [hkn, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, WPMonadExact.wp_pure_eq]
      rw [ofNat_succ]
      exact ih (n - (k + 1)) (by omega) (k + 1) _ rfl (by omega) (by simp [ho]) hset


section
variable [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)

theorem wp_zipWithAddL {m : DataMem} {A B O rsp : BitVec 64} {n : Nat} (h : ZipArrays m A B O rsp n) :
    wp (zipWithAddL s ra A B O (BitVec.ofNat 64 n) rsp) (fun _ _ => False)
      (fun l m' => l = .exit ∧ words m' O n = List.zipWith (· + ·) (words m A n) (words m B n),
        estack⟨⟩) m := by
  have hl := h.layout
  have hT := Refinement.transport
    (zipWithAddArr.refines s ra A B O rsp n (words m A n).toArray (words m B n).toArray)
    (Pa := (· = outView O n m)) (Qa := fun _ _ => False)
    (Ea := (fun (l : CfgLabel) (o : Array (BitVec 64)) => l = CfgLabel.exit ∧
      o = Array.zipWith (· + ·) (words m A n).toArray (words m B n).toArray, estack⟨⟩))
    ⟨fun o ho => by
      subst ho
      exact wp_zipWithAddArr s ra A B O rsp hl.len hl.sizeA hl.sizeB (by simp [outView, words])⟩
  refine WP.wp_monotone (x := zipWithAddL s ra A B O (BitVec.ofNat 64 n) rsp) ?_ ?_ m
    (hT.le_wp m (by
      simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]
      exact ⟨⟨PureRefinement.of_rel trivial, PureRefinement.of_rel trivial, hl⟩, trivial⟩))
  · intro _ m' hq
    rw [Concretization.post_pi] at hq
    obtain ⟨_, -, hq⟩ := hq
    exact hq.elim
  · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l m' he
    rw [Concretization.post_pi] at he
    obtain ⟨l', hll', hl', ho⟩ := he
    simp only [outView] at ho
    refine ⟨hll' ▸ hl', ?_⟩
    have := congrArg Array.toList ho
    simpa only [List.toList_toArray, Array.toList_zipWith] using this

/-- The pure program of `zipWithAdd`: the arrays of the inputs, added elementwise. -/
def zipWithAddP (a b : Array (BitVec 64)) : Id (Array (BitVec 64)) := pure (Array.zipWith (· + ·) a b)

/-- `zipWithAddArr` refines the pure program on its input arrays, under the concretization that
forgets the output array. The result is the output array at the return. -/
theorem zipWithAddArr_refines_P {A B O rsp : BitVec 64} {n : Nat} {a b o : Array (BitVec 64)}
    (hn : n < 2 ^ 61) (ha : a.size = n) (hb : b.size = n) (ho : o.size = n) :
    ⦃(· = o)⦄ (zipWithAddArr s ra A B O rsp n a b) ⪯[purify (Array (BitVec 64))]
      (zipWithAddP a b)
      ⦃fun _ _ _ => False; (fun l o' => l = .exit ∧ o' = Id.run (zipWithAddP a b), estack⟨⟩)⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro o' ho'
  simp only [meet_apply, meet_prop_eq_and] at ho'
  obtain ⟨rfl, -⟩ := ho'
  refine WP.wp_monotone (x := zipWithAddArr s ra A B O rsp n a b) ?_ ?_ _
    (wp_zipWithAddArr s ra A B O rsp hn ha hb ho)
  · intro _ _ hq
    exact hq.elim
  · exact Prod.mk_le _ _ _ (fun _ _ h => h) PartialOrder.rel_refl

/-! ## The machine code -/

/-- What the x64 text computes: started at `s.push64 ra` with `rdi`, `rsi`, `rdx` pointing to the
arrays and `rcx` holding their length `n`, it returns to `ra` with the stack pointer of the caller,
and the output array holds `List.zipWith (· + ·)` of the inputs. -/
theorem zipWithAdd_correct (s : MachineData) (ra : Int64) {A B O : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    Triple zipWithAdd (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
        ∧ words t.dmem O n = List.zipWith (· + ·) (words (s.push64 ra).dmem A n)
            (words (s.push64 ra).dmem B n)) := by
  let t₀ := s.push64 ra
  let rsp := t₀.regs.get64 .rsp
  let Ea : (CfgLabel → DataMem → Prop) × EStack⟨⟩ :=
    (fun l m' => l = .exit ∧ words m' O n = List.zipWith (· + ·) (words t₀.dmem A n) (words t₀.dmem B n),
      estack⟨⟩)
  have hL := Refinement.transport (zipWithAddL.refines s ra A B O (BitVec.ofNat 64 n) rsp)
    (Pa := (· = t₀.dmem)) ⟨fun m hm => by subst hm; exact wp_zipWithAddL s ra hmem⟩
    (Qa := fun _ _ => False) (Ea := Ea)
  have hT := Refinement.transport (zipWithAddT.refines s ra)
    (Pa := (· = abs t₀)) ⟨fun t ht => by
      subst ht
      refine hL.le_wp (abs t₀) ?_
      simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred, abs_regs, abs_dmem]
      exact ⟨⟨.of_rel hrdi, .of_rel hrsi, .of_rel hrdx, .of_rel hrcx, .of_rel rfl⟩, trivial⟩⟩
  refine ⟨fun t ht => ?_⟩
  refine WP.wp_monotone (x := zipWithAdd) ?_ ?_ t (hT.le_wp t ?_)
  · intro _ _ _
    trivial
  · intro a t' h'
    change (Concretization.ofStateRepr abs).post (RetRel s ra) _ a t' at h'
    rw [Concretization.post_pi] at h'
    obtain ⟨l', ⟨hra, -, hrsp⟩, h''⟩ := h'
    simp only [Concretization.ofStateRepr_pred, EPostsConcretization.ePosts_cons] at h''
    rw [Concretization.post_pi] at h''
    obtain ⟨_, -, -, hwords⟩ := h''
    exact ⟨hra, hrsp, hwords⟩
  · simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]
    exact ⟨ht, by rw [ht]⟩

end

end Ascent.Kraken
