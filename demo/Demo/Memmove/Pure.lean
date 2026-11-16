import Demo.Memmove.Arrays
import Demo.Zip.Pure

/-!
# `memmove` as a pure program

`memmoveArrays_spec` states the result of the array program: both loops exit with the destination
equal to the source array `a`. `vcgen` proves it with one invariant and one measure per loop. The
backward loop keeps the cells at and above its counter, the forward loop the cells below it.
`ascend_def` synthesizes the pure program `memmovePure` from this result, and `Refinement.comp_le`
composes the layers into `memmove_refines_Pure`, from the x64 text to `memmovePure` on the source bytes.
`memmove_correct` reads the destination array back as memory bytes.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred ofStateRepr_post_post)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken

theorem memmoveArrays_spec {ra : Int64} {n : Nat} {a : Array (BitVec 8)} (back : Bool) (ha : a.size = n) :
    ⦃(·.size = n)⦄ memmoveArrays ra n a back
      ⦃fun _ _ => False; (fun (l : Int64) (o' : Array (BitVec 8)) => l = ra ∧ o' = a, estack⟨⟩)⦄ := by
  vcgen [memmoveArrays]
    invariants
    · WhileInvariant.mk fun (done : Bool) (ik : Nat × Nat) (o' : Array (BitVec 8)) =>
        done = false ∧ 0 < ik.1 ∧ ik.1 ≤ n ∧ ik.2 = ik.1 ∧ o'.size = n ∧
          ∀ j, ik.1 ≤ j → j < n → o'[j]! = a[j]!
    · Variant.ofMeasure fun (ik : Nat × Nat) => ik.1
    · WhileInvariant.mk fun (done : Bool) (ik : Nat × Nat) (o' : Array (BitVec 8)) =>
        done = false ∧ ik.1 < n ∧ ik.2 = n ∧ o'.size = n ∧ ∀ j < ik.1, o'[j]! = a[j]!
    · Variant.ofMeasure fun (ik : Nat × Nat) => n - ik.1
    simp [Variant.evalsBelow_ofMeasure_nat]
    with finish

/-! ## The pure program -/

ascend_def memmovePure (ra : Int64) (n : Nat) (a : Array (BitVec 8)) (back : Bool) (ha : a.size = n) :
    Id (Array (BitVec 8)) from
  ⦃(·.size = n)⦄ (memmoveArrays ra n a back) ⪯[purify (Array (BitVec 8))] memmovePure
    ⦃fun _ _ _ => False; (fun l o => l = ra ∧ o = Id.run memmovePure, estack⟨⟩)⦄
  ascend [wrp_purify_throw (memmoveArrays_spec back ha)] with finish

/-! ## The chain of refinements -/

/-- The memory at the entry of `memmove`: the source `S` and the destination `O` of `n` mapped
bytes, apart from each other, and the destination apart from the return slot at `rsp`. -/
structure MoveBytes (m : DataMem) (S O rsp : BitVec 64) (n : Nat) : Prop where
  len : n < 2 ^ 61
  mapS : Mem.Mapped [(S, 1 * n)] m
  mapO : Mem.Mapped [(O, 1 * n)] m
  disj : Mem.Blocks.Disjoint [(O, 1 * n)] [(S, 1 * n)]
  disjR : Mem.Blocks.Disjoint [(rsp, 8)] [(O, 1 * n)]

@[grind =] theorem size_bytes_toArray (m : DataMem) (p : BitVec 64) (n : Nat) :
    (words 1 8 m p n).toArray.size = n := by
  simp [words]

@[grind →] theorem MoveBytes.layout {m : DataMem} {S O rsp : BitVec 64} {n : Nat} {ra : Int64}
    (h : MoveBytes m S O rsp n) (hr : retAddrAt m rsp = some ra) :
    ArrayLayout 1 8 [(S, (words 1 8 m S n).toArray)] O n [(rsp, ra)] m where
  width := by omega
  bits := rfl
  len := h.len
  mapped := h.mapO
  inputs := ⟨by refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [size_bytes_toArray]
                · exact h.len
                · exact h.mapS
                · exact h.disj, trivial⟩
  reserved := ⟨⟨hr, h.disjR⟩, trivial⟩

noncomputable abbrev memToBytes (O : BitVec 64) (n : Nat) :=
  ((ofStateRepr MachineData.dmem).comp (ofStateRepr (outView 1 8 O n))).comp (purify (Array (BitVec 8)))

noncomputable abbrev machineToBytes (O : BitVec 64) (n : Nat) := (ofStateRepr abs).comp (memToBytes O n)

attribute [grind =] memmovePure

section
variable [Host] [Embeds memmove] (r₀ : BitVec 64) (ra : Int64)

theorem memmoveLoops_refines_Arrays {O S : BitVec 64} {n : Nat} {a : Array (BitVec 8)} {back : Bool} :
    ⦃fun t => RegsRel [(.rdi, O), (.rsi, S), (.rdx, BitVec.ofNat 64 n), (.rsp, r₀)] t ∧
      (CondCode.nc.cmp O S ≐ back ∧ S ≐ₐ a ∧ a.size = n ∧ ArrayLayout 1 8 [(S, a)] O n [(r₀, ra)] t.dmem)⦄
      (memmoveLoops r₀ ra) ⪯[(ofStateRepr MachineData.dmem).comp (ofStateRepr (outView 1 8 O n))]
      (memmoveArrays ra n a back)
      ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rax = O ∧
        t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄ := by
  exact Refinement.comp_le (by grind) (by grind) (by grind) (memmoveArrays.refines O S r₀ ra n a back)
    ((memmoveRegs.refines O S (BitVec.ofNat 64 n) r₀ ra).weaken fun t h => h.1)

theorem memmoveLoops_refines_Pure {O S : BitVec 64} {n : Nat} {a : Array (BitVec 8)} {back : Bool}
    (ha : a.size = n) :
    ⦃fun t => RegsRel [(.rdi, O), (.rsi, S), (.rdx, BitVec.ofNat 64 n), (.rsp, r₀)] t ∧
      (CondCode.nc.cmp O S ≐ back ∧ S ≐ₐ a ∧ a.size = n ∧ ArrayLayout 1 8 [(S, a)] O n [(r₀, ra)] t.dmem)⦄
      (memmoveLoops r₀ ra) ⪯[memToBytes O n] (memmovePure a)
      ⦃fun _ _ _ => False; (fun l t => l = ra ∧ t.regs.get64 .rax = O ∧
        t.regs.get64 .rsp = r₀ + 8 ∧
        outView 1 8 O n t.dmem = Id.run (memmovePure a), estack⟨⟩)⦄ := by
  exact Refinement.comp_le (by grind) (by grind) (by grind) (memmovePure.refines ra n a back ha)
    (memmoveLoops_refines_Arrays r₀ ra)

end

section
variable [Host] [FunDecls] [Embeds memmove] (s : MachineData) (ra : Int64)

theorem memmove_refines_Pure {O S : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = O) (hrsi : (s.push64 ra).regs.get64 .rsi = S)
    (hrdx : (s.push64 ra).regs.get64 .rdx = BitVec.ofNat 64 n)
    (hmem : MoveBytes (s.push64 ra).dmem S O ((s.push64 ra).regs.get64 .rsp) n) :
    ⦃(· = s.push64 ra)⦄ memmove
      ⪯[machineToBytes O n] (memmovePure (words 1 8 (s.push64 ra).dmem S n).toArray)
      ⦃fun _ _ _ => False; fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        t.regs.get64 .rax = O ∧
        outView 1 8 O n t.dmem = Id.run (memmovePure (words 1 8 (s.push64 ra).dmem S n).toArray)⦄ := by
  have hr : retAddrAt (s.push64 ra).dmem ((s.push64 ra).regs.get64 .rsp) = some ra := by
    have h := MachineData.retAddr_push64 s ra
    rw [MachineData.retAddr_eq] at h
    exact h
  exact Refinement.comp_le (by grind) (by grind) (by grind)
    (memmoveLoops_refines_Pure ((s.push64 ra).regs.get64 .rsp) ra (S := S) (back := CondCode.nc.cmp O S) (size_bytes_toArray _ _ _))
    ((memmoveLoops.refines ((s.push64 ra).regs.get64 .rsp) ra).weaken fun t ht => by
      subst ht; exact ⟨rfl, MachineData.retAddr_push64 s ra⟩)

/-- What the x64 text of `memmove` computes on disjoint regions: started at `s.push64 ra` with
`rdi` pointing to the destination, `rsi` to the source and `rdx` holding the length `n`, it returns
to `ra` with the stack pointer of the caller and `rax` holding the destination, and the destination
holds the bytes of the source. -/
theorem memmove_correct {O S : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = O) (hrsi : (s.push64 ra).regs.get64 .rsi = S)
    (hrdx : (s.push64 ra).regs.get64 .rdx = BitVec.ofNat 64 n)
    (hmem : MoveBytes (s.push64 ra).dmem S O ((s.push64 ra).regs.get64 .rsp) n) :
    Triple memmove (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧ t.regs.get64 .rax = O
        ∧ words 1 8 t.dmem O n = words 1 8 (s.push64 ra).dmem S n) := by
  have h := (memmove_refines_Pure s ra hrdi hrsi hrdx hmem).transport
    (Pa := True) (Qa := fun _ => True) (Ea := estack⟨⟩) ⟨fun _ => trivial⟩
  refine ⟨fun t ht => WP.wp_monotone (x := memmove) (fun _ _ _ => trivial) ?_ t (h.le_wp t (by grind))⟩
  intro a t hE
  grind

end

end Ascent.Kraken
