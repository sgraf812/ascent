import Demo.ZipArr

/-!
# What `zipWithAdd` computes, from the array program

`zipWithAddArr_spec` states the result of the synthesized array program `zipWithAddArr`: it exits
with the output array `Array.zipWith (· + ·) a b`. `vcgen` proves it with the loop invariant
"the first `i` cells hold the sums" and the measure `n - i`, and `finish` closes the verification
conditions. `ascend_def` synthesizes the pure program `zipWithAddP` from this result through
`wrp_purify_throw`.

`Refinement.comp_le` composes the refinements of the layers into `zipWithAdd_refines_P`, from the
x64 text to `zipWithAddP` on the input arrays. `zipWithAdd_correct` is one `Refinement.transport`
of it, with the output array read back as memory words.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred ofStateRepr_post_post)
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
    (A B O rsp : BitVec 64) {n : Nat} {a b : Array (BitVec 64)} (ha : a.size = n) (hb : b.size = n) :
    ⦃(·.size = n)⦄ zipWithAddArr s ra A B O rsp n a b
      ⦃fun _ _ => False; (fun (l : CfgLabel) (o' : Array (BitVec 64)) =>
        l = .exit ∧ o' = Array.zipWith (· + ·) a b, estack⟨⟩)⦄ := by
  vcgen [zipWithAddArr]
    invariants
    · WhileInvariant.mk fun (done : Bool) (i : Nat) (o' : Array (BitVec 64)) =>
        done = false ∧ i < n ∧ o'.size = n ∧ ∀ j < i, o'[j]! = a[j]! + b[j]!
    · Variant.ofMeasure fun (i : Nat) => n - i
    simp [Variant.evalsBelow_ofMeasure_nat]
    with finish

/-! ## The pure program -/

ascend_def zipWithAddP [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)
    (A B O rsp : BitVec 64) (n : Nat) (a b : Array (BitVec 64)) (ha : a.size = n) (hb : b.size = n) :
    Id (Array (BitVec 64)) from
  ⦃(·.size = n)⦄ (zipWithAddArr s ra A B O rsp n a b) ⪯[purify (Array (BitVec 64))] zipWithAddP
    ⦃fun _ _ _ => False; (fun l o => l = .exit ∧ o = Id.run zipWithAddP, estack⟨⟩)⦄
  ascend [wrp_purify_throw (zipWithAddArr_spec s ra A B O rsp ha hb)] with finish

/-! ## The chain of refinements -/

noncomputable abbrev memToArray (O : BitVec 64) (n : Nat) :=
  ((ofStateRepr MachineData.dmem).comp (ofStateRepr (outView O n))).comp (purify (Array (BitVec 64)))

noncomputable abbrev machineToArray (O : BitVec 64) (n : Nat) := (ofStateRepr abs).comp (memToArray O n)

section
variable [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)

theorem zipWithAddT_refines_Arr {A B O rsp : BitVec 64} {n : Nat} {a b : Array (BitVec 64)} :
    ⦃fun t => RegsRel [(.rdi, A), (.rsi, B), (.rdx, O), (.rcx, BitVec.ofNat 64 n), (.rsp, rsp)] t ∧
      (A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout [(A, a), (B, b)] O n [rsp] t.dmem)⦄
      (zipWithAddT s ra) ⪯[(ofStateRepr MachineData.dmem).comp (ofStateRepr (outView O n))]
      (zipWithAddArr s ra A B O rsp n a b) ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ := by
  refine Refinement.comp_le ?_ ?_ ?_ (zipWithAddArr.refines s ra A B O rsp n a b)
    ((zipWithAddL.refines s ra A B O (BitVec.ofNat 64 n) rsp).weaken fun t h => h.1)
  · intro Qa cv cs h
    rw [ofStateRepr_post_post, Concretization.post_pi] at h
    obtain ⟨av, -, h⟩ := h
    exact (Concretization.post_pi _ _ _ _ _).mpr ⟨av, trivial, h⟩
  · intro Ea
    refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l cs h
    simp only [EPostsConcretization.ePosts_cons, ofStateRepr_post_post] at h ⊢
    rw [Concretization.post_pi] at h ⊢
    obtain ⟨l', ⟨l'', h₁, h₂⟩, h⟩ := h
    exact ⟨l', h₁.trans h₂, h⟩
  · intro X t h
    simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at h ⊢
    exact ⟨h.1.2, h.2⟩

theorem zipWithAddT_refines_P {A B O rsp : BitVec 64} {n : Nat} {a b : Array (BitVec 64)}
    (ha : a.size = n) (hb : b.size = n) :
    ⦃fun t => RegsRel [(.rdi, A), (.rsi, B), (.rdx, O), (.rcx, BitVec.ofNat 64 n), (.rsp, rsp)] t ∧
      (A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout [(A, a), (B, b)] O n [rsp] t.dmem)⦄
      (zipWithAddT s ra)
      ⪯[memToArray O n]
      (zipWithAddP s ra A B O rsp n a b ha hb)
      ⦃fun _ _ _ => False; (fun l t => l = .exit ∧
        outView O n t.dmem = Id.run (zipWithAddP s ra A B O rsp n a b ha hb), estack⟨⟩)⦄ := by
  refine Refinement.comp_le ?_ ?_ ?_ (zipWithAddP.refines s ra A B O rsp n a b ha hb)
    (zipWithAddT_refines_Arr s ra)
  · intro Qa cv cs h
    simp only [Concretization.post_pi, Concretization.comp_pred, ofStateRepr_pred, false_and,
      exists_false, and_false] at h
  · intro Ea
    refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l cs h
    simp only [EPostsConcretization.ePosts_cons_fill] at h
    rw [Concretization.post_pi] at h
    obtain ⟨l', rfl, h⟩ := h
    exact h
  · intro X t h
    simp only [meet_apply, meet_prop_eq_and, Concretization.comp_pred, ofStateRepr_pred] at h ⊢
    exact ⟨size_words_toArray _ _ _, h.2⟩

theorem zipWithAdd_refines_P {A B O : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    ⦃(· = s.push64 ra)⦄ zipWithAdd
      ⪯[machineToArray O n]
      (zipWithAddP s ra A B O ((s.push64 ra).regs.get64 .rsp) n
        (words (s.push64 ra).dmem A n).toArray (words (s.push64 ra).dmem B n).toArray
        (size_words_toArray _ _ _) (size_words_toArray _ _ _))
      ⦃fun _ _ _ => False; fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        outView O n t.dmem = Id.run (zipWithAddP s ra A B O ((s.push64 ra).regs.get64 .rsp) n
          (words (s.push64 ra).dmem A n).toArray (words (s.push64 ra).dmem B n).toArray
          (size_words_toArray _ _ _) (size_words_toArray _ _ _))⦄ := by
  refine Refinement.comp_le ?_ ?_ ?_ (zipWithAddT_refines_P s ra _ _) (zipWithAddT.refines s ra)
  · intro Qa cv cs h
    simp only [Concretization.post_pi, Concretization.comp_pred, ofStateRepr_pred, false_and,
      exists_false, and_false] at h
  · intro Ea a t h
    change (ofStateRepr abs).post (RetRel s ra) _ a t at h
    rw [Concretization.post_pi] at h
    obtain ⟨l, ⟨hra, -, hrsp⟩, -, h⟩ := h
    simp only [abs_dmem] at h
    exact ⟨hra, hrsp, h⟩
  · intro X t h
    simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at h ⊢
    obtain ⟨rfl, hX⟩ := h
    refine ⟨⟨?_, PureRefinement.of_rel trivial, PureRefinement.of_rel trivial,
      size_words_toArray _ _ _, size_words_toArray _ _ _, ?_⟩, hX⟩
    · simp only [abs_regs, RegsRel]
      exact ⟨.of_rel hrdi, .of_rel hrsi, .of_rel hrdx, .of_rel hrcx, .of_rel rfl, trivial⟩
    · simpa only [abs_dmem] using hmem.layout

/-! ## The machine code -/

theorem words_eq_zipWith_of_outView {m m' : DataMem} {A B O : BitVec 64} {n : Nat}
    (h : outView O n m' = Array.zipWith (· + ·) (words m A n).toArray (words m B n).toArray) :
    words m' O n = List.zipWith (· + ·) (words m A n) (words m B n) := by
  have := congrArg Array.toList h
  simpa only [outView, List.toList_toArray, Array.toList_zipWith] using this

/-- What the x64 text computes: started at `s.push64 ra` with `rdi`, `rsi`, `rdx` pointing to the
arrays and `rcx` holding their length `n`, it returns to `ra` with the stack pointer of the caller,
and the output array holds `List.zipWith (· + ·)` of the inputs. -/
theorem zipWithAdd_correct {A B O : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    Triple zipWithAdd (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
        ∧ words t.dmem O n = List.zipWith (· + ·) (words (s.push64 ra).dmem A n)
            (words (s.push64 ra).dmem B n)) := by
  have h := (zipWithAdd_refines_P s ra hrdi hrsi hrdx hrcx hmem).transport
    (Pa := True) (Qa := fun _ => True) (Ea := estack⟨⟩) ⟨fun _ => trivial⟩
  refine ⟨fun t ht => WP.wp_monotone (x := zipWithAdd) (fun _ _ _ => trivial) ?_ t
    (h.le_wp t (by simp only [meet_apply, meet_prop_eq_and, Concretization.comp_pred,
      ofStateRepr_pred, purify_pred]; exact ⟨ht, trivial⟩))⟩
  rintro a t ⟨hra, hrsp, ho⟩
  exact ⟨hra, hrsp, words_eq_zipWith_of_outView ho⟩

end

end Ascent.Kraken
