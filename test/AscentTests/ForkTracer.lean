import Ascent.Tactic.VCGen.Frontend
import Ascent.Refinement.StateRepr
import Ascent.UB.StateT
import Std.Tactic.Do

open Std.WP Lean.Order Ascent Ascent.Concretization

set_option experimental.vcgen true

namespace ForkTracer

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

@[ascend high] theorem setL_stutter {β AV : Type} (x : String) (v : Nat) (k : Unit → M β)
    (a : StateT Nat UB AV) (Q : β → AV → St → Prop) (E : EStack⟨⟩) :
    (fun s => wp (setL x v) (fun u s' => s'.heap = s.heap ∧
        wrp (ofStateRepr St.heap) (k u) a Q E s') E s)
      ⊑ wrp (ofStateRepr St.heap) (setL x v >>= k) a Q E :=
  wrp_stutter St.heap (setL x v) k a Q E

@[ascend] theorem getL_read (x : String) (av : Nat) (Q : Nat → Nat → St → Prop)
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

/-- Reads the heap of the concrete state. -/
def getH : M Nat := fun s => pure (s.heap, s)

@[spec] theorem getH_spec (post : Nat → St → Prop) : ⦃fun s => post s.heap s⦄ getH ⦃post⦄ :=
  ⟨fun s h => by simpa [StateT.wp_apply_eq, StateT.run, getH, UB.wp_pure_eq] using h⟩

@[ascend] theorem getH_read (av : Nat) (Q : Nat → Nat → St → Prop) (E : EStack⟨⟩) :
    (fun s => wp getH (fun v s' => s'.heap = s.heap ∧ Q v av s') E s)
      ⊑ wrp (ofStateRepr St.heap) getH (pure av : StateT Nat UB Nat) Q E :=
  wrp_read St.heap getH av Q E

/-- The only abstract value for `getH` is the concrete `s.heap`, so the synthesized program would
mention the concrete state, and the final scope check fails. -/
example : True := by
  fail_if_success
    have : ∃ a : StateT Nat UB Nat,
        ⦃(⊤ : St → Prop)⦄ getH ⪯[ofStateRepr St.heap] a ⦃fun cv av => ⌜cv = av⌝⦄ := by
      apply Exists.intro
      ascend'
  trivial

end ForkTracer
