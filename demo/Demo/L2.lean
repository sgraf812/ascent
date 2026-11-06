import Demo.Zip
import Demo.BlockRefine

/-!
# The second layer

The abstract state of the second layer is `RegMem`: the general-purpose registers as a function
`Reg64 → BitVec 64` and the data memory. `regMem` reads it off a `MachineData`, which forgets the
status flags and the vector registers. The first layer writes no flag, so every step of the first
layer has an exact counterpart here, and `refines_cfgLoop` carries the block table across.

Words stay `BitVec 64`: the machine adds modulo `2 ^ 64`, and so does `List.zipWith (· + ·)` on
`BitVec 64`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken
open Ascent.Concretization (ofStateRepr)

set_option experimental.vcgen true

namespace Ascent.Kraken

structure RegMem where
  regs : Reg64 → BitVec 64
  mem : DataMem

def regMem (s : MachineData) : RegMem := ⟨s.regs.get64, s.dmem⟩

def RegMem.set (st : RegMem) (r : Reg64) (v : BitVec 64) : RegMem :=
  { st with regs := fun r' => if r' = r then v else st.regs r' }

@[simp, vcgen_simp, grind =] theorem regMem_regs (s : MachineData) :
    (regMem s).regs = s.regs.get64 := rfl
@[simp, vcgen_simp, grind =] theorem regMem_mem (s : MachineData) : (regMem s).mem = s.dmem := rfl
@[simp, vcgen_simp, grind =] theorem RegMem.set_regs (st : RegMem) (r r' : Reg64) (v : BitVec 64) :
    (st.set r v).regs r' = if r' = r then v else st.regs r' := rfl
@[simp, vcgen_simp, grind =] theorem RegMem.set_mem (st : RegMem) (r : Reg64) (v : BitVec 64) :
    (st.set r v).mem = st.mem := rfl

theorem regMem_set64 (s : MachineData) (r : Reg64) (v : BitVec 64) :
    regMem { s with regs := s.regs.set64 r v } = (regMem s).set r v := by
  simp only [regMem, RegMem.set, RegMem.mk.injEq, and_true]
  funext r'
  exact Reg64s.get64_set64 s.regs r r' v

namespace RInstr

/-! ## The steps

Each step is the step of the first layer with `st.regs.get64 r` read as `st.regs r`. -/

noncomputable def movRegSib8 (r b i : Reg64) (d : Int64) : BlockM RegMem Unit :=
  let a (st : RegMem) := st.regs b + st.regs i * 8 + BitVec.ofInt 64 d.toInt
  AInstr.modifyIf (fun st => (Mem.loadInt st.mem (a st) 8).isSome = true) fun st =>
    st.set r (BitVec.ofInt 64 (Mem.loadInt st.mem (a st) 8).get!)

noncomputable def addRegSib8 (rd b i : Reg64) (d : Int64) : BlockM RegMem Unit :=
  let a (st : RegMem) := st.regs b + st.regs i * 8 + BitVec.ofInt 64 d.toInt
  AInstr.modifyIf (fun st => (Mem.loadInt st.mem (a st) 8).isSome = true) fun st =>
    st.set rd (BitVec.ofInt 64 (Mem.loadInt st.mem (a st) 8).get! + st.regs rd)

noncomputable def movSib8Reg (b i : Reg64) (d : Int64) (rs : Reg64) : BlockM RegMem Unit :=
  let a (st : RegMem) := st.regs b + st.regs i * 8 + BitVec.ofInt 64 d.toInt
  AInstr.modifyIf (fun st => (Mem.loadInt st.mem (a st) 8).isSome = true
      ∧ Mem.Blocks.Disjoint [(st.regs .rsp, 8)] [(a st, 8)]) fun st =>
    { st with mem := Mem.storeInt st.mem (a st) 8 (st.regs rs).toInt }

noncomputable def incReg (r : Reg64) : BlockM RegMem Unit :=
  AInstr.modifyIf (fun _ => True) fun st => st.set r (st.regs r + 1)

noncomputable def xorReg32Reg32 (rd rs : Reg64) : BlockM RegMem Unit :=
  AInstr.modifyIf (fun _ => True) fun st =>
    st.set rd (((st.regs rd).take 32 ^^^ (st.regs rs).take 32).zeroExtend 64)

def cmpJcc (ra rb : Reg64) (cc : CondCode) (l : Label) : BlockM RegMem Unit :=
  AInstr.branch (fun st => cc.cmp (st.regs ra) (st.regs rb)) (.label l)

def testJcc (ra rb : Reg64) (cc : CondCode) (l : Label) : BlockM RegMem Unit :=
  AInstr.branch (fun st => cc.cmp (st.regs ra &&& st.regs rb) 0) (.label l)

noncomputable def ret : BlockM RegMem Unit :=
  AInstr.exitIf (fun st => (Mem.loadInt st.mem (st.regs .rsp) 8).isSome = true)
    (fun st => st.set .rsp (st.regs .rsp + 8)) .exit

/-! ## The rules -/

section
variable {Q : Unit → Unit → MachineData → Prop}
  {E : (CfgLabel → CfgLabel → MachineData → Prop) × EStack⟨⟩}

@[ascend] theorem wrp_movRegSib8 (r b i : Reg64) (d : Int64) :
    (fun s =>
      let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 8).isSome = true →
        Q () () { s with regs := s.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!) })
      ⊑ wrp (ofStateRepr regMem) (AInstr.movRegSib8 r b i d) (movRegSib8 r b i d) Q E :=
  by
  unfold AInstr.movRegSib8 movRegSib8
  dsimp only
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf_repr regMem _ _ (fun _ h => ?_) fun s _ => ?_)
  all_goals first | exact regMem_set64 _ _ _ | rfl | exact fun _ h => h | assumption

@[ascend] theorem wrp_addRegSib8 (rd b i : Reg64) (d : Int64) :
    (fun s =>
      let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 8).isSome = true →
        Q () () { s with regs := s.regs.set64 rd (BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get! + s.regs.get64 rd) })
      ⊑ wrp (ofStateRepr regMem) (AInstr.addRegSib8 rd b i d) (addRegSib8 rd b i d) Q E :=
  by
  unfold AInstr.addRegSib8 addRegSib8
  dsimp only
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf_repr regMem _ _ (fun _ h => ?_) fun s _ => ?_)
  all_goals first | exact regMem_set64 _ _ _ | rfl | exact fun _ h => h | assumption

@[ascend] theorem wrp_movSib8Reg (b i : Reg64) (d : Int64) (rs : Reg64) :
    (fun s =>
      let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
      (Mem.loadInt s.dmem a 8).isSome = true ∧ Mem.Blocks.Disjoint [(s.regs.get64 .rsp, 8)] [(a, 8)] →
        Q () () { s with dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 rs).toInt })
      ⊑ wrp (ofStateRepr regMem) (AInstr.movSib8Reg b i d rs) (movSib8Reg b i d rs) Q E :=
  by
  unfold AInstr.movSib8Reg movSib8Reg
  dsimp only
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf_repr regMem _ _ (fun _ h => ?_) fun _ _ => ?_)
  all_goals first | exact regMem_set64 _ _ _ | rfl | exact fun _ h => h | assumption

@[ascend] theorem wrp_incReg (r : Reg64) :
    (fun s => True → Q () () { s with regs := s.regs.set64 r (s.regs.get64 r + 1) })
      ⊑ wrp (ofStateRepr regMem) (AInstr.incReg r) (incReg r) Q E :=
  by
  unfold AInstr.incReg incReg
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf_repr regMem _ _ (fun _ h => ?_) fun s _ => ?_)
  all_goals first | exact regMem_set64 _ _ _ | rfl | exact fun _ h => h | assumption

@[ascend] theorem wrp_xorReg32Reg32 (rd rs : Reg64) :
    (fun s => True → Q () () { s with regs := s.regs.set64 rd (((s.regs.get64 rd).take 32 ^^^ (s.regs.get64 rs).take 32).zeroExtend 64) })
      ⊑ wrp (ofStateRepr regMem) (AInstr.xorReg32Reg32 rd rs) (xorReg32Reg32 rd rs) Q E :=
  by
  unfold AInstr.xorReg32Reg32 xorReg32Reg32
  refine PartialOrder.rel_trans ?_ (wrp_modifyIf_repr regMem _ _ (fun _ h => ?_) fun s _ => ?_)
  all_goals first | exact regMem_set64 _ _ _ | rfl | exact fun _ h => h | assumption

@[ascend] theorem wrp_cmpJcc (ra rb : Reg64) (cc : CondCode) (l : Label) :
    (fun s => (cc.cmp (s.regs.get64 ra) (s.regs.get64 rb) = true → E.1 (.label l) (.label l) s)
        ∧ (cc.cmp (s.regs.get64 ra) (s.regs.get64 rb) = false → Q () () s))
      ⊑ wrp (ofStateRepr regMem) (AInstr.cmpJcc ra rb cc l) (cmpJcc ra rb cc l) Q E :=
  by
  unfold AInstr.cmpJcc cmpJcc
  refine PartialOrder.rel_trans ?_ (wrp_branch_repr regMem _ (fun _ => ?_) _)
  all_goals first | exact regMem_set64 _ _ _ | rfl | exact fun _ h => h | assumption

@[ascend] theorem wrp_testJcc (ra rb : Reg64) (cc : CondCode) (l : Label) :
    (fun s => (cc.cmp (s.regs.get64 ra &&& s.regs.get64 rb) 0 = true → E.1 (.label l) (.label l) s)
        ∧ (cc.cmp (s.regs.get64 ra &&& s.regs.get64 rb) 0 = false → Q () () s))
      ⊑ wrp (ofStateRepr regMem) (AInstr.testJcc ra rb cc l) (testJcc ra rb cc l) Q E :=
  by
  unfold AInstr.testJcc testJcc
  refine PartialOrder.rel_trans ?_ (wrp_branch_repr regMem _ (fun _ => ?_) _)
  all_goals first | exact regMem_set64 _ _ _ | rfl | exact fun _ h => h | assumption

@[ascend] theorem wrp_ret :
    (fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).isSome = true →
        E.1 .exit .exit { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8) })
      ⊑ wrp (ofStateRepr regMem) AInstr.ret ret Q E :=
  by
  unfold AInstr.ret ret
  refine PartialOrder.rel_trans ?_ (wrp_exitIf_repr regMem _ _ (fun _ h => ?_) (fun s _ => ?_) _)
  all_goals first | exact regMem_set64 _ _ _ | rfl | exact fun _ h => h | assumption

end

end RInstr

attribute [ascend] wrp_bind wrp_pure_unit
attribute [local vcgen_simp] zipWithAdd

open RInstr in
ascend_def zipWithAddR [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    BlockM RegMem Unit from
  ⦃(fun _ => True)⦄ (zipWithAddA s ra) ⪯[ofStateRepr regMem] zipWithAddR
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [zipWithAddA,
    refines_cfgLoop (Concretization.ofStateRepr_pred_iSup regMem) (I := fun _ => True)]
  with finish

open RInstr in
/-- The program of the second layer: the blocks of the first layer over `RegMem`. -/
example [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64) :
    zipWithAddR s ra = cfgLoop (Table.get [
      (.entry, do
        testJcc .rcx .rcx .le "LBB0_3"
        xorReg32Reg32 .rax .rax
        pure ()),
      (.label "LBB0_2", do
        movRegSib8 .r8 .rsi .rax 0
        addRegSib8 .r8 .rdi .rax 0
        movSib8Reg .rdx .rax 0 .r8
        incReg .rax
        cmpJcc .rcx .rax .nz "LBB0_2"
        pure ()),
      (.label "LBB0_3", ret)]) (Program.next zipWithAdd) .entry := rfl

end Ascent.Kraken
