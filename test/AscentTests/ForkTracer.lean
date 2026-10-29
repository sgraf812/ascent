import Ascent.Tactic.VCGen.Frontend
import Ascent.UB.StateT
import Std.Tactic.Do

open Std.WP Lean.Order Ascent Ascent.Concretization

set_option experimental.vcgen true

namespace ForkTracer

variable {Cσ Aσ CV CV₂ AV : Type}

theorem wrp_stutter (f : Cσ → Aσ) (c₁ : StateT Cσ UB CV) (c₂ : CV → StateT Cσ UB CV₂)
    (a : StateT Aσ UB AV) (Q : CV₂ → AV → Cσ → Prop) (E : EStack⟨⟩) :
    (fun s => wp c₁ (fun v s' => f s' = f s ∧ wrp (ofStateRepr f) (c₂ v) a Q E s') E s)
      ⊑ wrp (ofStateRepr f) (c₁ >>= c₂) a Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and] at hs
  obtain ⟨h, ha⟩ := hs
  rw [wp_bind_StateT]
  refine WP.wp_monotone_post (x := c₁) ?_ s h
  rintro v s' ⟨hf, hw⟩
  refine wrp_transport (P := wrp (ofStateRepr f) (c₂ v) a Q E) PartialOrder.rel_refl Qa Ea s' ?_
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at ha ⊢
  rw [hf]
  exact ⟨hw, ha⟩

theorem wrp_read (f : Cσ → Aσ) (c : StateT Cσ UB CV) (av : AV) (Q : CV → AV → Cσ → Prop)
    (E : EStack⟨⟩) :
    (fun s => wp c (fun v s' => f s' = f s ∧ Q v av s') E s)
      ⊑ wrp (ofStateRepr f) c (pure av : StateT Aσ UB AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and] at hs
  obtain ⟨h, ha⟩ := hs
  simp only [ofStateRepr_pred, StateT.wp_apply_eq, StateT.run_pure, UB.wp_pure_eq] at ha
  refine WP.wp_monotone_post (x := c) ?_ s h
  rintro v s' ⟨hf, hq⟩
  simp only [post_pi, ofStateRepr_pred]
  exact ⟨av, hq, by rw [hf]; exact ha⟩

structure St where
  locals : String → Option Nat
  heap : Nat

abbrev M := StateT St UB

def getL (x : String) : M Nat := fun s =>
  match s.locals x with
  | some v => pure (v, s)
  | none => UB.fail

def setL (x : String) (v : Nat) : M Unit := fun s =>
  pure ((), { s with locals := fun y => if y = x then some v else s.locals y })

@[spec] theorem getL_spec (x : String) (post : Nat → St → Prop) :
    ⦃fun s => match s.locals x with | some v => post v s | none => False⦄ getL x ⦃post⦄ := by
  refine ⟨fun s h => ?_⟩
  simp only [StateT.wp_apply_eq, StateT.run]
  unfold getL
  split <;> simp_all [UB.wp_pure_eq]

@[spec] theorem setL_spec (x : String) (v : Nat) (post : Unit → St → Prop) :
    ⦃fun s => post () { s with locals := fun y => if y = x then some v else s.locals y }⦄
      setL x v ⦃post⦄ := by
  refine ⟨fun s h => ?_⟩
  simp only [StateT.wp_apply_eq, StateT.run, setL, UB.wp_pure_eq]
  exact h

@[wrp_spec high] theorem setL_stutter {β AV : Type} (x : String) (v : Nat) (k : Unit → M β)
    (a : StateT Nat UB AV) (Q : β → AV → St → Prop) (E : EStack⟨⟩) :
    (fun s => wp (setL x v) (fun u s' => s'.heap = s.heap ∧
        wrp (ofStateRepr St.heap) (k u) a Q E s') E s)
      ⊑ wrp (ofStateRepr St.heap) (setL x v >>= k) a Q E :=
  wrp_stutter St.heap (setL x v) k a Q E

@[wrp_spec] theorem getL_read (x : String) (av : Nat) (Q : Nat → Nat → St → Prop)
    (E : EStack⟨⟩) :
    (fun s => wp (getL x) (fun v s' => s'.heap = s.heap ∧ Q v av s') E s)
      ⊑ wrp (ofStateRepr St.heap) (getL x) (pure av : StateT Nat UB Nat) Q E :=
  wrp_read St.heap (getL x) av Q E

/-- The engine synthesizes `pure m`: the stutter spec takes `setL`, and the read spec takes
`getL`. -/
def synth (m : Nat) : { a : StateT Nat UB Nat //
    ⦃(⊤ : St → Prop)⦄ (setL "n" m >>= fun _ => getL "n") ⪯[ofStateRepr St.heap] a
      ⦃fun cv av => ⌜cv = av⌝⦄ } := by
  apply Subtype.mk
  ascend'
  simp
  rfl

example (m : Nat) : (synth m).1 = pure m := rfl

/-- With the abstract program given, the same engine checks the refinement. -/
example (m : Nat) :
    ⦃(⊤ : St → Prop)⦄ (setL "n" m >>= fun _ => getL "n") ⪯[ofStateRepr St.heap]
      (pure m : StateT Nat UB Nat) ⦃fun cv av => ⌜cv = av⌝⦄ := by
  ascend'
  simp

end ForkTracer
