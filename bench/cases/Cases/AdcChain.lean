import Cases.Setup.State

/-!
# `AdcChain`: accessor-style rules on a carry chain

The mirror of the `vcgen` case `AdcChain`, in `SM S` with two registers and a carry flag. Each
`adc` adds `rbx` and the carry into `rax` and recomputes the carry. Each rule quantifies the
continuation over a fresh post-state, characterized by one equation per component, so that the run
accumulates a system of equations on the concrete states. The family stresses goals whose concrete
state is a fresh variable at each step.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.AdcChain

structure S where
  rax : BitVec 64
  rbx : BitVec 64
  cf  : Bool

def movRax (i : BitVec 64) : SM S Unit := modify fun s => { s with rax := i }

def movRbx (i : BitVec 64) : SM S Unit := modify fun s => { s with rbx := i }

def adc : SM S Unit := modify fun s =>
  let v := s.rax + s.rbx + BitVec.ofNat 64 s.cf.toNat
  { rax := v, rbx := s.rbx,
    cf := v.toNat != s.rax.toNat + s.rbx.toNat + s.cf.toNat }

theorem wp_movRax (i : BitVec 64) (Q : Unit → S → Prop) (E : EStack⟨⟩) (s : S) :
    wp (movRax i) Q E s = Q () { s with rax := i } := rfl
theorem wp_movRbx (i : BitVec 64) (Q : Unit → S → Prop) (E : EStack⟨⟩) (s : S) :
    wp (movRbx i) Q E s = Q () { s with rbx := i } := rfl
theorem wp_adc (Q : Unit → S → Prop) (E : EStack⟨⟩) (s : S) :
    wp adc Q E s = Q () ⟨s.rax + s.rbx + BitVec.ofNat 64 s.cf.toNat, s.rbx,
      (s.rax + s.rbx + BitVec.ofNat 64 s.cf.toNat).toNat != s.rax.toNat + s.rbx.toNat + s.cf.toNat⟩ :=
  rfl

section
variable {Q : Unit → Unit → S → Prop} {E : EStack⟨⟩}

@[distill] theorem wrp_movRax (i : BitVec 64) :
    (fun s => ∀ s' : S, s'.rax = i → s'.rbx = s.rbx → s'.cf = s.cf → Q () () s')
      ⊑ wrp (γ S) (movRax i) (movRax i) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_movRax] at h ⊢
  rw [Concretization.post_pi]
  exact ⟨(), h.1 _ rfl rfl rfl, h.2⟩

@[distill] theorem wrp_movRbx (i : BitVec 64) :
    (fun s => ∀ s' : S, s'.rax = s.rax → s'.rbx = i → s'.cf = s.cf → Q () () s')
      ⊑ wrp (γ S) (movRbx i) (movRbx i) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_movRbx] at h ⊢
  rw [Concretization.post_pi]
  exact ⟨(), h.1 _ rfl rfl rfl, h.2⟩

@[distill] theorem wrp_adc :
    (fun s => ∀ s' : S,
        s'.rax = s.rax + s.rbx + BitVec.ofNat 64 s.cf.toNat →
        s'.rbx = s.rbx →
        s'.cf = ((s.rax + s.rbx + BitVec.ofNat 64 s.cf.toNat).toNat
                  != s.rax.toNat + s.rbx.toNat + s.cf.toNat) →
        Q () () s')
      ⊑ wrp (γ S) adc adc Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_adc] at h ⊢
  rw [Concretization.post_pi]
  exact ⟨(), h.1 _ rfl rfl rfl, h.2⟩

end

attribute [distill] wrp_bind wrp_pure_unit_SM

def chain : Nat → SM S Unit
  | 0 => pure ()
  | n+1 => do adc; chain n

def prog (n : Nat) : SM S Unit := do
  movRax 1
  movRbx 3
  chain n

end DistillBench.AdcChain
