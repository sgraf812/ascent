import Ascent.Corres.Refinement
import Ascent.UB

/-!
# A heap swap refinement (aliasing)

A pointer swap implemented by read-both/write-both abstracts to the atomic swap specification,
*provided the pointers do not alias*. Aliasing surfaces as the `p ≠ q` guard on the abstract
spec: without it the two heap transformers differ (writing `q` would clobber the value just
written to `p`). The guard lives in the `UB` effect, so when `p = q` the spec fails and
the refinement is discharged trivially. This is the split-heap picture in miniature: one heap,
pointer (in)equality carrying the aliasing, no separation logic.
-/

open Std.WP Lean.Order Ascent

/-- A heap: address to value. -/
abbrev Heap := Nat → Int

/-- Point update. -/
def upd (p : Nat) (v : Int) (h : Heap) : Heap := fun a => if a = p then v else h a

/-- Atomic swap of the values at `p` and `q` (the spec). -/
def swapSpec (p q : Nat) (h : Heap) : Heap := fun a => if a = p then h q else if a = q then h p else h a

/-- Read both, then write both (the implementation). -/
def swapImpl (p q : Nat) (h : Heap) : Heap := upd q (h p) (upd p (h q) h)

/-- Under non-aliasing, the implementation and the spec are the same heap transformer. -/
theorem swapImpl_eq_spec {p q : Nat} (hpq : p ≠ q) : swapImpl p q = swapSpec p q := by
  funext h a
  simp only [swapImpl, swapSpec, upd]
  by_cases hap : a = p <;> by_cases haq : a = q <;> simp_all

/-- Abstract spec: atomic swap, guarded by non-aliasing. As a `StateT Heap UB` program this is
the denotation of `do guardS (p ≠ q); modify (swapSpec p q)`; failure (`none`) is
`UB.fail`. -/
def swapA (p q : Nat) : StateT Heap UB PUnit :=
  fun h => if p ≠ q then pure (⟨⟩, swapSpec p q h) else UB.fail

/-- Concrete implementation: the denotation of `modify (swapImpl p q)`. -/
def swapC (p q : Nat) : StateT Heap UB PUnit :=
  fun h => some (⟨⟩, swapImpl p q h)

theorem wp_swapC (p q : Nat) (Q : PUnit → Heap → Prop) (E : EPost.Nil) :
    wp (swapC p q) Q E = fun h => Q ⟨⟩ (swapImpl p q h) := rfl

theorem wp_swapA (p q : Nat) (Q : PUnit → Heap → Prop) (E : EPost.Nil) :
    wp (swapA p q) Q E = fun h => if p ≠ q then Q ⟨⟩ (swapSpec p q h) else ⊥ := by
  funext h
  simp only [swapA, StateT.wp_apply_eq, StateT.run, wp_ite, UB.wp_pure_eq, UB.wp_fail_eq]

/-- The read-both/write-both swap abstracts to the atomic spec under non-aliasing. -/
example (p q : Nat) :
    ⦃(⊤ : Heap → Prop)⦄ (swapC p q) ⪯[Concretization.id (Heap → Prop) EPost.Nil] (swapA p q)
      ⦃(⌜· = ·⌝)⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  show wp (swapA p q) Qa Ea ⊑ wp (swapC p q) _ Ea
  rw [wp_swapA, wp_swapC]
  intro h hpre
  by_cases hpq : p ≠ q
  · rw [ite_eq_left hpq] at hpre
    rw [swapImpl_eq_spec hpq]
    simp only [Concretization.post_pi, Concretization.id, id_eq,
      CompleteLattice.ofProp_apply, ofProp_prop_eq]
    exact ⟨⟨⟩, trivial, hpre⟩
  · rw [ite_eq_right hpq, bot_prop_eq] at hpre
    exact hpre.elim
