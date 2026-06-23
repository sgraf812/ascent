import Ascent.Corres.Basic
import AscentTests.Guard

/-!
# A heap swap correspondence (aliasing)

A pointer swap implemented by read-both/write-both abstracts to the atomic swap specification,
*provided the pointers do not alias*. Aliasing surfaces as the `p ≠ q` guard on the abstract
spec: without it the two heap transformers differ (writing `q` would clobber the value just
written to `p`). The guard lives in the `UB` effect, so when `p = q` the spec fails and
the correspondence is discharged trivially. This is the split-heap picture in miniature: one heap,
pointer (in)equality carrying the aliasing, no separation logic.
-/

open Std.Internal.Do Lean.Order Ascent

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
  fun h => if p ≠ q then some (⟨⟩, swapSpec p q h) else none

/-- Concrete implementation: the denotation of `modify (swapImpl p q)`. -/
def swapC (p q : Nat) : StateT Heap UB PUnit :=
  fun h => some (⟨⟩, swapImpl p q h)

theorem wp_swapC (p q : Nat) (Q : PUnit → Heap → Prop) (E : EPost.Nil) :
    wp (swapC p q) Q E = fun h => Q ⟨⟩ (swapImpl p q h) := rfl

theorem wp_swapA (p q : Nat) (Q : PUnit → Heap → Prop) (E : EPost.Nil) :
    wp (swapA p q) Q E = fun h => if p ≠ q then Q ⟨⟩ (swapSpec p q h) else ⊥ := by
  funext h
  unfold swapA
  by_cases hpq : p ≠ q
  · simp only [if_pos hpq]; rfl
  · simp only [if_neg hpq]; rfl

/-- The read-both/write-both swap abstracts to the atomic spec under non-aliasing. -/
example (p q : Nat) :
    Corres (idRefinement (Heap → Prop) EPost.Nil) (id : PUnit → PUnit) (swapA p q) (swapC p q) := by
  intro Q E
  show wp (swapA p q) Q E ⊑ wp (swapC p q) Q E
  rw [wp_swapA, wp_swapC]
  intro h
  dsimp only
  by_cases hpq : p ≠ q
  · rw [if_pos hpq, swapImpl_eq_spec hpq]
  · rw [if_neg hpq]; exact bot_le _
