import Cases.Setup.State

/-!
# `RegFile`: a register file as the state

The mirror of the `vcgen` case `RegFile`, in `SM Regs`. Each step adds `1` to each of the eight
registers through the accessors `Regs.get` and `Regs.set`. The `@[vcgen_simp]` theorems turn
`s.set .rK v` into a structure literal and `(Regs.mk …).rK` into a field, so the run keeps the
concrete state as one `Regs.mk` literal. The family stresses the simplification of the state
argument of each goal.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.RegFile

inductive R where
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7

structure Regs where
  r0 : BitVec 64
  r1 : BitVec 64
  r2 : BitVec 64
  r3 : BitVec 64
  r4 : BitVec 64
  r5 : BitVec 64
  r6 : BitVec 64
  r7 : BitVec 64

def Regs.get (s : Regs) : R → BitVec 64
  | .r0 => s.r0
  | .r1 => s.r1
  | .r2 => s.r2
  | .r3 => s.r3
  | .r4 => s.r4
  | .r5 => s.r5
  | .r6 => s.r6
  | .r7 => s.r7

def Regs.set (s : Regs) (r : R) (v : BitVec 64) : Regs :=
  match r with
  | .r0 => { s with r0 := v }
  | .r1 => { s with r1 := v }
  | .r2 => { s with r2 := v }
  | .r3 => { s with r3 := v }
  | .r4 => { s with r4 := v }
  | .r5 => { s with r5 := v }
  | .r6 => { s with r6 := v }
  | .r7 => { s with r7 := v }

@[vcgen_simp] theorem Regs.set_r0 (s : Regs) (v : BitVec 64) : s.set .r0 v = { s with r0 := v } := rfl
@[vcgen_simp] theorem Regs.set_r1 (s : Regs) (v : BitVec 64) : s.set .r1 v = { s with r1 := v } := rfl
@[vcgen_simp] theorem Regs.set_r2 (s : Regs) (v : BitVec 64) : s.set .r2 v = { s with r2 := v } := rfl
@[vcgen_simp] theorem Regs.set_r3 (s : Regs) (v : BitVec 64) : s.set .r3 v = { s with r3 := v } := rfl
@[vcgen_simp] theorem Regs.set_r4 (s : Regs) (v : BitVec 64) : s.set .r4 v = { s with r4 := v } := rfl
@[vcgen_simp] theorem Regs.set_r5 (s : Regs) (v : BitVec 64) : s.set .r5 v = { s with r5 := v } := rfl
@[vcgen_simp] theorem Regs.set_r6 (s : Regs) (v : BitVec 64) : s.set .r6 v = { s with r6 := v } := rfl
@[vcgen_simp] theorem Regs.set_r7 (s : Regs) (v : BitVec 64) : s.set .r7 v = { s with r7 := v } := rfl
@[vcgen_simp] theorem Regs.get_r0 (s : Regs) : s.get .r0 = s.r0 := rfl
@[vcgen_simp] theorem Regs.get_r1 (s : Regs) : s.get .r1 = s.r1 := rfl
@[vcgen_simp] theorem Regs.get_r2 (s : Regs) : s.get .r2 = s.r2 := rfl
@[vcgen_simp] theorem Regs.get_r3 (s : Regs) : s.get .r3 = s.r3 := rfl
@[vcgen_simp] theorem Regs.get_r4 (s : Regs) : s.get .r4 = s.r4 := rfl
@[vcgen_simp] theorem Regs.get_r5 (s : Regs) : s.get .r5 = s.r5 := rfl
@[vcgen_simp] theorem Regs.get_r6 (s : Regs) : s.get .r6 = s.r6 := rfl
@[vcgen_simp] theorem Regs.get_r7 (s : Regs) : s.get .r7 = s.r7 := rfl
@[vcgen_simp] theorem Regs.r0_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r0 = a0 := rfl
@[vcgen_simp] theorem Regs.r1_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r1 = a1 := rfl
@[vcgen_simp] theorem Regs.r2_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r2 = a2 := rfl
@[vcgen_simp] theorem Regs.r3_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r3 = a3 := rfl
@[vcgen_simp] theorem Regs.r4_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r4 = a4 := rfl
@[vcgen_simp] theorem Regs.r5_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r5 = a5 := rfl
@[vcgen_simp] theorem Regs.r6_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r6 = a6 := rfl
@[vcgen_simp] theorem Regs.r7_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r7 = a7 := rfl

attribute [vcgen_simp] BitVec.add_assoc

def addi (d a : R) (i : BitVec 64) : SM Regs Unit := modify fun s => s.set d (s.get a + i)

theorem wp_addi (d a : R) (i : BitVec 64) (Q : Unit → Regs → Prop) (E : EStack⟨⟩) (s : Regs) :
    wp (addi d a i) Q E s = Q () (s.set d (s.get a + i)) := rfl

@[distill] theorem wrp_addi (d a : R) (i : BitVec 64) {Q : Unit → Unit → Regs → Prop} {E : EStack⟨⟩} :
    (fun s => Q () () (s.set d (s.get a + i))) ⊑ wrp (γ Regs) (addi d a i) (addi d a i) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_addi] at h ⊢
  rw [Concretization.post_pi]
  exact ⟨(), h.1, h.2⟩

attribute [distill] wrp_bind wrp_pure_unit_SM

def step : SM Regs Unit := do
  addi .r0 .r0 1
  addi .r1 .r1 1
  addi .r2 .r2 1
  addi .r3 .r3 1
  addi .r4 .r4 1
  addi .r5 .r5 1
  addi .r6 .r6 1
  addi .r7 .r7 1

def loop (n : Nat) : SM Regs Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

end DistillBench.RegFile
