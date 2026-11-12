import Demo.ZipArr

/-!
# What `zipWithAdd` computes, from the array program

`zipWithAddArr_spec` states the result of the synthesized array program `zipWithAddArr`: it exits
with the output array `Array.zipWith (· + ·) a b`. `vcgen` proves it with the loop invariant
"the first `i` cells hold the sums" and the measure `n - i`, and `finish` closes the verification
conditions. `ascend_def` synthesizes the pure program `zipWithAddP` from this result through
`wrp_purify_throw`.

`Refinement.comp_le` composes the refinements of the layers into `zipWithAdd_refines_P`, from the
x64 text to `zipWithAddP` on the input arrays. `grind` closes the side conditions of each
composition: the concretization lemmas are `grind norm` rules, and the facts that the next layer
assumes, such as `ZipArrays.layout`, are `grind` rules next to their definitions.
`zipWithAdd_correct` is one `Refinement.transport` of the composition, with the output array read
back as memory words.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred ofStateRepr_post_post)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken

/-- The memory at the entry of `zipWithAdd`: arrays `A`, `B` and `O` of `n` mapped words, the output
array apart from the inputs, and all three apart from the return slot at `rsp`. -/
structure ZipArrays (m : DataMem) (A B O rsp : BitVec 64) (n : Nat) : Prop where
  len : n < 2 ^ 61
  mapA : Mem.Mapped [(A, 8 * n)] m
  mapB : Mem.Mapped [(B, 8 * n)] m
  mapO : Mem.Mapped [(O, 8 * n)] m
  disjA : Mem.Blocks.Disjoint [(O, 8 * n)] [(A, 8 * n)]
  disjB : Mem.Blocks.Disjoint [(O, 8 * n)] [(B, 8 * n)]
  apart : ZipApart (Fr rsp 0 0) A B O n

attribute [grind →] ZipArrays.apart

@[grind =] theorem size_words_toArray (m : DataMem) (p : BitVec 64) (n : Nat) : (words 8 64 m p n).toArray.size = n := by
  simp [words]

theorem ZipArrays.inputAt {m : DataMem} {O p : BitVec 64} {n : Nat} (hn : n < 2 ^ 61)
    (hmap : Mem.Mapped [(p, 8 * n)] m) (hd : Mem.Blocks.Disjoint [(O, 8 * n)] [(p, 8 * n)]) :
    InputAt 8 64 m O n p (words 8 64 m p n).toArray := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [size_words_toArray]
  · exact hn
  · exact hmap
  · exact hd

@[grind →] theorem ZipArrays.layout {m : DataMem} {A B O rsp : BitVec 64} {n : Nat}
    (h : ZipArrays m A B O rsp n) :
    ArrayLayout 8 64 [(A, (words 8 64 m A n).toArray), (B, (words 8 64 m B n).toArray)] O n []
      (FState.split (Fr rsp 0 0) m).dmem where
  width := by omega
  bits := rfl
  len := h.len
  mapped := Mapped.split h.mapO h.apart.2.2
  inputs := ⟨(ZipArrays.inputAt h.len h.mapA h.disjA).split (by omega)
      (by rw [size_words_toArray]; exact h.apart.1),
    (ZipArrays.inputAt h.len h.mapB h.disjB).split (by omega)
      (by rw [size_words_toArray]; exact h.apart.2.1), trivial⟩
  reserved := trivial

theorem zipWithAddArr_spec {ra : Int64} {n : Nat} {a b : Array (BitVec 64)} (ha : a.size = n)
    (hb : b.size = n) :
    ⦃(·.size = n)⦄ zipWithAddArr ra n a b
      ⦃fun _ _ => False; (fun (l : Int64) (o' : Array (BitVec 64)) =>
        l = ra ∧ o' = Array.zipWith (· + ·) a b, estack⟨⟩)⦄ := by
  vcgen [zipWithAddArr]
    invariants
    · WhileInvariant.mk fun (done : Bool) (i : Nat) (o' : Array (BitVec 64)) =>
        done = false ∧ i < n ∧ o'.size = n ∧ ∀ j < i, o'[j]! = a[j]! + b[j]!
    · Variant.ofMeasure fun (i : Nat) => n - i
    simp [Variant.evalsBelow_ofMeasure_nat]
    with finish

/-! ## The pure program -/

ascend_def zipWithAddP (ra : Int64) (n : Nat) (a b : Array (BitVec 64)) (ha : a.size = n)
    (hb : b.size = n) : Id (Array (BitVec 64)) from
  ⦃(·.size = n)⦄ (zipWithAddArr ra n a b) ⪯[purify (Array (BitVec 64))] zipWithAddP
    ⦃fun _ _ _ => False; (fun l o => l = ra ∧ o = Id.run zipWithAddP, estack⟨⟩)⦄
  ascend [wrp_purify_throw (zipWithAddArr_spec ha hb)] with finish

/-! ## The chain of refinements -/

attribute [grind =] zipWithAddP

noncomputable abbrev memToArray (r₀ O : BitVec 64) (n : Nat) :=
  ((ofStateRepr MachineData.dmem).comp ((ofStateRepr (FState.split (Fr r₀ 0 0))).comp
    (ofStateRepr fun s : FState => outView 8 64 O n s.dmem))).comp (purify (Array (BitVec 64)))

noncomputable abbrev machineToArray (r₀ O : BitVec 64) (n : Nat) :=
  (ofStateRepr abs).comp (memToArray r₀ O n)

@[grind =] theorem stackAddr_eq {a x : BitVec 64} : StackAddr a x = (a = x) := rfl

section
variable [Host] [FunDecls] [Embeds zipWithAdd] (r₀ : BitVec 64) (ra : Int64)

theorem zipWithAddL₀_refines_Arr {A B O : BitVec 64} {n : Nat} {a b : Array (BitVec 64)} :
    ⦃fun m => (r₀ ≐ₛ r₀ ∧ retAddrAt m r₀ = some ra) ∧
      (A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧
        ArrayLayout 8 64 [(A, a), (B, b)] O n [] (FState.split (Fr r₀ 0 0) m).dmem ∧
        ZipApart (Fr r₀ 0 0) A B O n)⦄
      (zipWithAddL₀ A B O (BitVec.ofNat 64 n) r₀ r₀ ra)
      ⪯[(ofStateRepr (FState.split (Fr r₀ 0 0))).comp (ofStateRepr fun s : FState => outView 8 64 O n s.dmem)]
      (zipWithAddArr ra n a b)
      ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  Refinement.comp_le (by grind) (by grind) (by grind) (zipWithAddArr.refines A B O r₀ ra n a b)
    ((zipWithAddF.refines A B O (BitVec.ofNat 64 n) r₀ r₀ ra).weaken fun _ h => h.1)

theorem zipWithAddT_refines_Arr {A B O : BitVec 64} {n : Nat} {a b : Array (BitVec 64)} :
    ⦃fun t => RegsRel [(.rdi, A), (.rsi, B), (.rdx, O), (.rcx, BitVec.ofNat 64 n),
        (.rsp, r₀)] t ∧
      ((r₀ ≐ₛ r₀ ∧ retAddrAt t.dmem r₀ = some ra) ∧
        (A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧
          ArrayLayout 8 64 [(A, a), (B, b)] O n [] (FState.split (Fr r₀ 0 0) t.dmem).dmem ∧
          ZipApart (Fr r₀ 0 0) A B O n))⦄
      (zipWithAddT r₀ ra)
      ⪯[(ofStateRepr MachineData.dmem).comp ((ofStateRepr (FState.split (Fr r₀ 0 0))).comp
        (ofStateRepr fun s : FState => outView 8 64 O n s.dmem))]
      (zipWithAddArr ra n a b)
      ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄ :=
  Refinement.comp_le (by grind) (by grind) (by grind) (zipWithAddL₀_refines_Arr r₀ ra)
    ((zipWithAddL₀.refines A B O (BitVec.ofNat 64 n) r₀ r₀ ra).weaken fun _ h => h.1)

theorem zipWithAddT_refines_P {A B O : BitVec 64} {n : Nat} {a b : Array (BitVec 64)}
    (ha : a.size = n) (hb : b.size = n) :
    ⦃fun t => RegsRel [(.rdi, A), (.rsi, B), (.rdx, O), (.rcx, BitVec.ofNat 64 n),
        (.rsp, r₀)] t ∧
      ((r₀ ≐ₛ r₀ ∧ retAddrAt t.dmem r₀ = some ra) ∧
        (A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧
          ArrayLayout 8 64 [(A, a), (B, b)] O n [] (FState.split (Fr r₀ 0 0) t.dmem).dmem ∧
          ZipApart (Fr r₀ 0 0) A B O n))⦄
      (zipWithAddT r₀ ra)
      ⪯[memToArray r₀ O n]
      (zipWithAddP a b)
      ⦃fun _ _ _ => False; (fun l t => l = ra ∧ t.regs.get64 .rsp = r₀ + 8 ∧
        outView 8 64 O n (FState.split (Fr r₀ 0 0) t.dmem).dmem = Id.run (zipWithAddP a b), estack⟨⟩)⦄ := by
  exact Refinement.comp_le (by grind) (by grind) (by grind) (zipWithAddP.refines ra n a b ha hb)
    (zipWithAddT_refines_Arr r₀ ra)

end

section
variable [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)

theorem zipWithAdd_refines_P {A B O : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    ⦃(· = s.push64 ra)⦄ zipWithAdd
      ⪯[machineToArray ((s.push64 ra).regs.get64 .rsp) O n]
      (zipWithAddP (words 8 64 (s.push64 ra).dmem A n).toArray
        (words 8 64 (s.push64 ra).dmem B n).toArray)
      ⦃fun _ _ _ => False; fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        outView 8 64 O n (FState.split (Fr ((s.push64 ra).regs.get64 .rsp) 0 0) t.dmem).dmem
          = Id.run (zipWithAddP (words 8 64 (s.push64 ra).dmem A n).toArray
            (words 8 64 (s.push64 ra).dmem B n).toArray)⦄ := by
  have hr : retAddrAt (s.push64 ra).dmem ((s.push64 ra).regs.get64 .rsp) = some ra := by
    have h := MachineData.retAddr_push64 s ra
    rw [MachineData.retAddr_eq] at h
    exact h
  exact Refinement.comp_le (by grind) (by grind) (by grind)
    (zipWithAddT_refines_P ((s.push64 ra).regs.get64 .rsp) ra (A := A) (B := B) (size_words_toArray _ _ _)
      (size_words_toArray _ _ _))
    ((zipWithAddT.refines ((s.push64 ra).regs.get64 .rsp) ra).weaken fun t ht => by
      subst ht; exact ⟨rfl, MachineData.retAddr_push64 s ra⟩)

/-! ## The machine code -/

omit [Host] [FunDecls] [Embeds zipWithAdd] in
@[grind →] theorem words_eq_zipWith_of_outView {m m' : DataMem} {A B O : BitVec 64} {n : Nat}
    (h : outView 8 64 O n m' = Array.zipWith (· + ·) (words 8 64 m A n).toArray (words 8 64 m B n).toArray) :
    words 8 64 m' O n = List.zipWith (· + ·) (words 8 64 m A n) (words 8 64 m B n) := by
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
        ∧ words 8 64 t.dmem O n = List.zipWith (· + ·) (words 8 64 (s.push64 ra).dmem A n)
            (words 8 64 (s.push64 ra).dmem B n)) := by
  have h := (zipWithAdd_refines_P s ra hrdi hrsi hrdx hrcx hmem).transport
    (Pa := True) (Qa := fun _ => True) (Ea := estack⟨⟩) ⟨fun _ => trivial⟩
  refine ⟨fun t ht => WP.wp_monotone (x := zipWithAdd) (fun _ _ _ => trivial) ?_ t (h.le_wp t (by grind))⟩
  intro a t hE
  have hO := hmem.apart.2.2
  have hn := hmem.len
  grind [outView_split]
end

end Ascent.Kraken
