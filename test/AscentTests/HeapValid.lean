import Ascent.Corres.Basic
import Ascent.UB

/-!
# `is_valid`-guarded heap access

A heap is a *partial* map: an unallocated address is `none` (invalid). Load and store live in
`StateT VHeap UB` and `guard` on validity, so an access to an invalid address is undefined behavior
(`wp = ⊥`). The consequence is the "no invalid access" guarantee: any provable Hoare triple about
a program built from these accesses must establish validity in its precondition, otherwise the
weakest precondition is `⊥` and nothing follows. This is AutoCorres' `c_guard`, on the concrete
side: the obligation to prove validity is what verifies the program never dereferences an invalid
pointer.
-/

open Std.WP Lean.Order Ascent

/-- A heap: address to value, partial (`none` = unallocated / invalid). -/
abbrev VHeap := Nat → Option Int

/-- Point update. -/
def updV (p : Nat) (v : Option Int) (h : VHeap) : VHeap := fun a => if a = p then v else h a

@[simp] theorem updV_self (p : Nat) (v : Option Int) (h : VHeap) : updV p v h p = v := by
  simp [updV]

/-- `wp` over `StateT VHeap UB` runs the program and reads off the result. -/
theorem wp_run {α} (x : StateT VHeap UB α) (Q : α → VHeap → Prop) (E : EPost.Nil) (h : VHeap) :
    wp x Q E h = match x h with | some (a, h') => Q a h' | none => (⊥ : Prop) := by
  rw [show wp x Q E h = wp (x h) (fun p : α × VHeap => Q p.1 p.2) E from rfl]
  cases hx : x h <;> rfl

/-- Guarded load: fail unless `p` is valid. -/
def loadV (p : Nat) : StateT VHeap UB Int := fun h => (h p).map (fun v => (v, h))

/-- Guarded store: fail unless `p` is valid. -/
def storeV (p : Nat) (v : Int) : StateT VHeap UB PUnit :=
  fun h => (h p).map (fun _ => (⟨⟩, updV p (some v) h))

/-- Loading guards on validity: an invalid address yields `⊥`. -/
theorem wp_loadV (p : Nat) (Q : Int → VHeap → Prop) (E : EPost.Nil) :
    wp (loadV p) Q E = fun h => match h p with | some v => Q v h | none => (⊥ : Prop) := by
  funext h; rw [wp_run]; cases hp : h p <;> simp [loadV, hp]

/-- Storing guards on validity. -/
theorem wp_storeV (p : Nat) (v : Int) (Q : PUnit → VHeap → Prop) (E : EPost.Nil) :
    wp (storeV p v) Q E = fun h => match h p with
      | some _ => Q ⟨⟩ (updV p (some v) h) | none => (⊥ : Prop) := by
  funext h; rw [wp_run]; cases hp : h p <;> simp [storeV, hp]

/-- Increment at `p`: the denotation of guarded load then guarded store (one validity guard). -/
def incr (p : Nat) : StateT VHeap UB PUnit :=
  fun h => (h p).map (fun v => (⟨⟩, updV p (some (v + 1)) h))

theorem wp_incr (p : Nat) (Q : PUnit → VHeap → Prop) (E : EPost.Nil) :
    wp (incr p) Q E = fun h => match h p with
      | some v => Q ⟨⟩ (updV p (some (v + 1)) h) | none => (⊥ : Prop) := by
  funext h; rw [wp_run]; cases hp : h p <;> simp [incr, hp]

/-- Functional correctness of `incr`, as a Hoare triple. The precondition `h p = some n` carries
validity; the postcondition records the incremented value. -/
example (p : Nat) (n : Int) :
    (fun h => h p = some n) ⊑ wp (incr p) (fun _ h => h p = some (n + 1)) EPost.Nil.mk := by
  rw [wp_incr]; intro h hpre; simp [hpre]

/-- The validity obligation cannot be dropped: with a trivial precondition the triple is false,
because `incr` fails on a heap where `p` is unallocated. -/
example (p : Nat) :
    ¬ ((fun _ => True) ⊑ wp (incr p) (fun _ _ => True) EPost.Nil.mk) := by
  rw [wp_incr]; intro hT; have h0 := hT (fun _ => none) trivial; simp at h0
