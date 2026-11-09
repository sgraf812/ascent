import Demo.BinaryCheck

/-!
# `zipWithAdd` as bytes

`zipWithAddBinary` holds the 28 bytes that `llvm-mc` assembles from the text of `zipWithAdd`, and
`zipWithAddSizes` the size of each directive of the text. `Binary.check` accepts them, so
`zipWithAddHost` lays out `zipWithAdd` from `Binary.base` and `zipWithAddHost_assembles` proves
`Binary.Assembles zipWithAdd zipWithAddBinary` at it.
-/

open Std.WP Lean.Order Ascent
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)
open scoped Program.WP

namespace Ascent.Kraken

def zipWithAddSizes : List Nat := [3, 2, 2, 0, 4, 4, 4, 3, 3, 2, 0, 1]

def zipWithAddBinary : ByteArray :=
  ⟨#[0x48, 0x85, 0xc9, 0x7e, 0x16, 0x31, 0xc0, 0x4c, 0x8b, 0x04, 0xc6, 0x4c, 0x03, 0x04, 0xc7,
    0x4c, 0x89, 0x04, 0xc2, 0x48, 0xff, 0xc0, 0x48, 0x39, 0xc1, 0x75, 0xec, 0xc3]⟩

theorem zipWithAddBinary_check : Binary.check zipWithAdd zipWithAddSizes zipWithAddBinary = true := by
  decide +kernel

@[instance_reducible] def zipWithAddHost : Host :=
  Host.ofCheck zipWithAdd zipWithAddSizes zipWithAddBinary zipWithAddBinary_check

theorem zipWithAddHost_assembles : @Binary.Assembles zipWithAddHost zipWithAdd zipWithAddBinary :=
  Binary.assembles_of_check zipWithAddBinary_check

section
variable [Host] (s : MachineData) (ra : Int64)

theorem zipWithAddBinary_refines_zipWithAdd (h : Binary.Assembles zipWithAdd zipWithAddBinary)
    (P : MachineData → Prop) :
    ⦃P⦄ zipWithAddBinary ⪯[ofStateRepr id] zipWithAdd ⦃fun _ _ _ => True; fun a a' _ => a = a'⦄ :=
  Binary.refines_program h P

theorem zipWithAddBinary_refines_P (h : Binary.Assembles zipWithAdd zipWithAddBinary) {A B O : BitVec 64}
    {n : Nat} (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    ⦃(· = s.push64 ra)⦄ zipWithAddBinary
      ⪯[(ofStateRepr id).comp (machineToArray O n)]
      (zipWithAddP (words 8 64 (s.push64 ra).dmem A n).toArray (words 8 64 (s.push64 ra).dmem B n).toArray)
      ⦃fun _ _ _ => False; fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        outView 8 64 O n t.dmem = Id.run (zipWithAddP (words 8 64 (s.push64 ra).dmem A n).toArray
          (words 8 64 (s.push64 ra).dmem B n).toArray)⦄ :=
  let _ : Embeds zipWithAdd := h.embeds
  Refinement.comp_le (by grind) (by grind) (by grind)
    (zipWithAdd_refines_P s ra hrdi hrsi hrdx hrcx hmem) (zipWithAddBinary_refines_zipWithAdd h _)

theorem zipWithAddBinary_correct (hasm : Binary.Assembles zipWithAdd zipWithAddBinary) {A B O : BitVec 64}
    {n : Nat} (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    Triple zipWithAddBinary (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
        ∧ words 8 64 t.dmem O n = List.zipWith (· + ·) (words 8 64 (s.push64 ra).dmem A n)
            (words 8 64 (s.push64 ra).dmem B n)) := by
  let _ : Embeds zipWithAdd := hasm.embeds
  have h := (zipWithAddBinary_refines_P s ra hasm hrdi hrsi hrdx hrcx hmem).transport
    (Pa := True) (Qa := fun _ => True) (Ea := estack⟨⟩) ⟨fun _ => trivial⟩
  refine ⟨fun t ht => WP.wp_monotone (x := zipWithAddBinary) (fun _ _ _ => trivial) ?_ t
    (h.le_wp t (by simp only [meet_apply, meet_prop_eq_and, Concretization.comp_pred,
      ofStateRepr_pred, purify_pred]; exact ⟨ht, trivial⟩))⟩
  rintro a t ⟨hra, hrsp, ho⟩
  exact ⟨hra, hrsp, words_eq_zipWith_of_outView ho⟩

end

theorem zipWithAddHost_correct (s : MachineData) (ra : Int64) {A B O : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    Triple zipWithAddBinary (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
        ∧ words 8 64 t.dmem O n = List.zipWith (· + ·) (words 8 64 (s.push64 ra).dmem A n)
            (words 8 64 (s.push64 ra).dmem B n)) :=
  @zipWithAddBinary_correct zipWithAddHost s ra zipWithAddHost_assembles A B O n hrdi hrsi hrdx hrcx hmem

end Ascent.Kraken
