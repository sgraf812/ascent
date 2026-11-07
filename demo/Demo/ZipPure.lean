import Demo.ZipArr

/-!
# What `zipWithAdd` computes, from the array program

`zipWithAddArr_spec` states the result of the synthesized array program `zipWithAddArr`: it exits
with the output array `Array.zipWith (· + ·) a b`. `vcgen` proves it with the loop invariant
"the first `v` cells hold the sums" and the measure `n - v`, and `finish` closes the verification
conditions. `wp_zipWithAddL` carries this result to the lifted program through
`zipWithAddArr.refines`, and `zipWithAdd_correct` carries it back to the x64 text through the
refinements of `zipWithAddL`, `zipWithAddT` and the first layer.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)
open scoped Program.WP

set_option experimental.vcgen true

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

theorem size_words_toArray (m : DataMem) (p : BitVec 64) (n : Nat) : (words m p n).toArray.size = n := by
  simp [words]

theorem ZipArrays.inputAt {m : DataMem} {O p : BitVec 64} {n : Nat} (hn : n < 2 ^ 61)
    (hmap : Mem.Mapped [(p, 8 * n)] m) (hd : Mem.Blocks.Disjoint [(O, 8 * n)] [(p, 8 * n)]) :
    InputAt m O n p (words m p n).toArray := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [size_words_toArray]
  · exact hn
  · exact hmap
  · exact hd

theorem ZipArrays.layout {m : DataMem} {A B O rsp : BitVec 64} {n : Nat}
    (h : ZipArrays m A B O rsp n) :
    ArrayLayout [(A, (words m A n).toArray), (B, (words m B n).toArray)] O n [rsp] m where
  len := h.len
  mapped := h.mapO
  inputs := ⟨ZipArrays.inputAt h.len h.mapA h.disjA, ZipArrays.inputAt h.len h.mapB h.disjB, trivial⟩
  reserved := ⟨⟨h.ret, h.disjR⟩, trivial⟩

theorem zipWithAddArr_spec [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)
    (A B O rsp : BitVec 64) {n : Nat} {a b o : Array (BitVec 64)} (hn : n < 2 ^ 61)
    (ha : a.size = n) (hb : b.size = n) (ho : o.size = n) :
    ⦃(· = o)⦄ zipWithAddArr s ra A B O rsp n a b
      ⦃fun _ _ => False; (fun (l : CfgLabel) (o' : Array (BitVec 64)) =>
        l = .exit ∧ o' = Array.zipWith (· + ·) a b, estack⟨⟩)⦄ := by
  vcgen [zipWithAddArr]
    invariants
    · WhileInvariant.mk fun (done : Bool) (v : BitVec 64) (o' : Array (BitVec 64)) =>
        done = false ∧ v.toNat < n ∧ o'.size = n ∧ ∀ i < v.toNat, o'[i]! = a[i]! + b[i]!
    · Variant.ofMeasure fun (v : BitVec 64) => n - v.toNat
    simp [toInt_ofNat_nonpos hn, Variant.evalsBelow_ofMeasure_nat]
    with finish

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
      exact (zipWithAddArr_spec s ra A B O rsp hl.len (size_words_toArray _ _ _) (size_words_toArray _ _ _)
        (by simp [outView, words])).le_wp _ rfl⟩
  refine WP.wp_monotone (x := zipWithAddL s ra A B O (BitVec.ofNat 64 n) rsp) ?_ ?_ m
    (hT.le_wp m (by
      simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]
      exact ⟨⟨PureRefinement.of_rel trivial, PureRefinement.of_rel trivial, size_words_toArray _ _ _,
        size_words_toArray _ _ _, hl⟩, trivial⟩))
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
    ((zipWithAddArr_spec s ra A B O rsp hn ha hb ho).le_wp _ rfl)
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
      simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred, abs_regs, abs_dmem, RegsRel]
      exact ⟨⟨.of_rel hrdi, .of_rel hrsi, .of_rel hrdx, .of_rel hrcx, .of_rel rfl, trivial⟩, trivial⟩⟩
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
