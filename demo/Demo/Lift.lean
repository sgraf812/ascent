import Demo.ZipStruct

/-!
# Register lifting

A program over `MachineData` refines a program over the data memory alone, under
`ofStateRepr MachineData.dmem`. A register read in the concrete program becomes a value of the
abstract program: the hypothesis `PureRefinement (t.regs.get64 r) x True Eq` relates the register
`r` of the state `t` to the abstract value `x`, and the `@[ascend_pure]` rules below abstract a
value computed from registers to the same computation on the abstract values. A step that writes a
register binds the abstract value of the written value to a variable of the abstract program.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Kraken

/-! ## Memory steps -/

/-- The eight-byte word at `a`, undefined behaviour when the cell is not mapped. -/
noncomputable def load8 (a : BitVec 64) : BlockM DataMem (BitVec 64) := fun m =>
  UB.guardRet ((Mem.loadInt m a 8).isSome = true) (.ok (BitVec.ofInt 64 (Mem.loadInt m a 8).get!), m)

/-- Store the word `v` at `a`, undefined behaviour unless the cell is mapped and apart from the
return slot at `rsp`. -/
noncomputable def store8 (rsp a v : BitVec 64) : BlockM DataMem Unit :=
  modifyIf (fun m => (Mem.loadInt m a 8).isSome = true ∧ Mem.Blocks.Disjoint [(rsp, 8)] [(a, 8)])
    fun m => Mem.storeInt m a 8 v.toInt

/-- Return through the return slot at `rsp`. -/
noncomputable def retAt (rsp : BitVec 64) : BlockM DataMem Unit :=
  exitIf (fun m => (Mem.loadInt m rsp 8).isSome = true) id .exit

section
variable (Q : BitVec 64 → DataMem → Prop) (Qu : Unit → DataMem → Prop)
  (E : (CfgLabel → DataMem → Prop) × EStack⟨⟩) (m : DataMem)

theorem wp_load8 (a : BitVec 64) :
    wp (load8 a) Q E m
      = ((Mem.loadInt m a 8).isSome = true ∧ Q (BitVec.ofInt 64 (Mem.loadInt m a 8).get!) m) := by
  rw [wp_BlockM_eq, show (load8 a).run.run m = load8 a m from rfl, load8]
  by_cases h : (Mem.loadInt m a 8).isSome = true
  · rw [UB.guardRet_of_pos h]
    simp only [h, true_and]
    rfl
  · rw [UB.guardRet_of_neg h, UB.fail_eq]
    simp only [Bool.not_eq_true] at h
    simp [h]

theorem wp_store8 (rsp a v : BitVec 64) :
    wp (store8 rsp a v) Qu E m
      = (((Mem.loadInt m a 8).isSome = true ∧ Mem.Blocks.Disjoint [(rsp, 8)] [(a, 8)])
          ∧ Qu () (Mem.storeInt m a 8 v.toInt)) := wp_modifyIf _ _ _ _ _

theorem wp_retAt (rsp : BitVec 64) :
    wp (retAt rsp) Qu E m = ((Mem.loadInt m rsp 8).isSome = true ∧ E.1 .exit m) :=
  wp_exitIf _ _ _ _ _ _

end

/-! ## The registers and the memory after a step -/

section
variable (st : MachineData)

@[vcgen_simp] theorem movRegSib8_regs (r b i : Reg64) (d : Int64) :
    (movRegSib8 r b i d st).regs
      = st.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt st.dmem (sib8 b i d st) 8).get!) := rfl
@[vcgen_simp] theorem movRegSib8_dmem (r b i : Reg64) (d : Int64) :
    (movRegSib8 r b i d st).dmem = st.dmem := rfl
@[vcgen_simp] theorem addRegSib8_regs (r b i : Reg64) (d : Int64) :
    (addRegSib8 r b i d st).regs = st.regs.set64 r
      (BitVec.ofInt 64 (Mem.loadInt st.dmem (sib8 b i d st) 8).get! + st.regs.get64 r) := rfl
@[vcgen_simp] theorem addRegSib8_dmem (r b i : Reg64) (d : Int64) :
    (addRegSib8 r b i d st).dmem = st.dmem := rfl
@[vcgen_simp] theorem movSib8Reg_regs (b i : Reg64) (d : Int64) (r : Reg64) :
    (movSib8Reg b i d r st).regs = st.regs := rfl
@[vcgen_simp] theorem movSib8Reg_dmem (b i : Reg64) (d : Int64) (r : Reg64) :
    (movSib8Reg b i d r st).dmem = Mem.storeInt st.dmem (sib8 b i d st) 8 (st.regs.get64 r).toInt := rfl
@[vcgen_simp] theorem incReg_regs (r : Reg64) :
    (incReg r st).regs = st.regs.set64 r (st.regs.get64 r + 1) := rfl
@[vcgen_simp] theorem incReg_dmem (r : Reg64) : (incReg r st).dmem = st.dmem := rfl
@[vcgen_simp] theorem xorReg32Reg32_regs (rd rs : Reg64) :
    (xorReg32Reg32 rd rs st).regs = st.regs.set64 rd
      (((st.regs.get64 rd).take 32 ^^^ (st.regs.get64 rs).take 32).zeroExtend 64) := rfl
@[vcgen_simp] theorem xorReg32Reg32_dmem (rd rs : Reg64) : (xorReg32Reg32 rd rs st).dmem = st.dmem :=
  rfl
@[vcgen_simp] theorem ret_regs : (ret st).regs = st.regs.set64 .rsp (st.regs.get64 .rsp + 8) := rfl
@[vcgen_simp] theorem ret_dmem : (ret st).dmem = st.dmem := rfl

end

/-! ## Values -/

section
variable {w : Nat} {a b x y : BitVec w} {P₁ P₂ : Prop}

@[ascend_pure] theorem abs_add (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_mul (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a * b) (x * y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_sib8 {t : MachineData} {b i : Reg64} {d : Int64} {x y : BitVec 64}
    (hb : PureRefinement (t.regs.get64 b) x P₁ Eq) (hi : PureRefinement (t.regs.get64 i) y P₂ Eq) :
    PureRefinement (sib8 b i d t) (x + y * 8 + BitVec.ofInt 64 d.toInt) (P₁ ∧ P₂) Eq :=
  fun ⟨hp₁, hp₂⟩ => by rw [sib8, hb hp₁, hi hp₂]

@[ascend_pure low] theorem abs_refl {α : Type} {c : α} : PureRefinement c c True Eq :=
  PureRefinement.of_rel rfl

end

/-! ## Steps -/

section
variable {Q : Unit → BitVec 64 → MachineData → Prop} {Qu : Unit → Unit → MachineData → Prop}
  {E : (CfgLabel → CfgLabel → MachineData → Prop) × EStack⟨⟩}

theorem wrp_pure_unit :
    Qu () () ⊑ wrp (ofStateRepr MachineData.dmem) (pure () : BlockM MachineData Unit)
      (pure () : BlockM DataMem Unit) Qu E :=
  wrp_pure () ()

theorem wrp_movRegSib8_load8 (r b i : Reg64) (d : Int64) (a : BitVec 64) :
    (fun t => PureRefinement (sib8 b i d t) a True Eq ∧
      (loadOk8 b i d t → ∀ y, PureRefinement ((movRegSib8 r b i d t).regs.get64 r) y True Eq →
        Q () y (movRegSib8 r b i d t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (loadOk8 b i d) (movRegSib8 r b i d))
          (load8 a) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_load8] at ht
  obtain ⟨⟨ha, hk⟩, hl, hq⟩ := ht
  have ha : sib8 b i d t = a := ha trivial
  have hg : loadOk8 b i d t := by rw [loadOk8, ha]; exact hl
  rw [wp_modifyIf, Concretization.post_pi]
  refine ⟨hg, _, hk hg _ (PureRefinement.of_rel ?_), hq⟩
  simp only [movRegSib8, Reg64s.get64_set64, ↓reduceIte, ha]

theorem wrp_addRegSib8_load8 (r b i : Reg64) (d : Int64) (a : BitVec 64) :
    (fun t => PureRefinement (sib8 b i d t) a True Eq ∧
      (loadOk8 b i d t →
        ∀ y, PureRefinement (BitVec.ofInt 64 (Mem.loadInt t.dmem (sib8 b i d t) 8).get!) y True Eq →
          Q () y (addRegSib8 r b i d t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (loadOk8 b i d) (addRegSib8 r b i d))
          (load8 a) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_load8] at ht
  obtain ⟨⟨ha, hk⟩, hl, hq⟩ := ht
  have ha : sib8 b i d t = a := ha trivial
  have hg : loadOk8 b i d t := by rw [loadOk8, ha]; exact hl
  rw [wp_modifyIf, Concretization.post_pi]
  refine ⟨hg, _, hk hg _ (PureRefinement.of_rel ?_), hq⟩
  rw [ha]

theorem wrp_movSib8Reg_store8 (b i : Reg64) (d : Int64) (rs : Reg64) (sp a v : BitVec 64) :
    (fun t => PureRefinement (t.regs.get64 .rsp) sp True Eq ∧ PureRefinement (sib8 b i d t) a True Eq ∧
      PureRefinement (t.regs.get64 rs) v True Eq ∧
      (storeOk8 b i d t → Qu () () (movSib8Reg b i d rs t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (storeOk8 b i d) (movSib8Reg b i d rs))
          (store8 sp a v) Qu E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_store8] at ht
  obtain ⟨⟨hsp, ha, hv, hk⟩, ⟨hl, hd⟩, hq⟩ := ht
  have hsp : t.regs.get64 .rsp = sp := hsp trivial
  have ha : sib8 b i d t = a := ha trivial
  have hv : t.regs.get64 rs = v := hv trivial
  have hg : storeOk8 b i d t := by rw [storeOk8, loadOk8, ha, hsp]; exact ⟨hl, hd⟩
  rw [wp_modifyIf, Concretization.post_pi]
  refine ⟨hg, (), hk hg, ?_⟩
  simp only [ofStateRepr_pred, movSib8Reg, ha, hv]
  exact hq

end

end Ascent.Kraken
