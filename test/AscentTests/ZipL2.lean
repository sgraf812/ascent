import AscentTests.Zip

/-!
# L2 (local-variable extraction), foundation

The concrete state `State` (untyped locals map + heap) is abstracted to just `Heap`. The state
abstraction is a real data refinement (`γP ≠ id`): an abstract heap-assertion `P` is concretized
to `fun s => couples s ∧ P s.heap`, where `couples` says the locals hold the expected values. The
meet (not implication) is what makes it sound: off the coupling the concretized assertion is `⊥`,
matching the fact that an extracted program makes no claim there.

The keystone lemma `corres_getSize` is the heart of local extraction: reading a coupled local
corresponds to using the λ-bound value, and the local's well-formedness (carried by `couples`)
discharges the projection-UB. From this plus `corres_bind`/`corres_store`/… the straight-line
program extracts; the loop (with an evolving coupling) is the next step.
-/

open Std.Internal.Do Lean.Order Ascent

namespace Zip

/-- `wp` over `StateT State UB` runs the program and reads off the result. -/
theorem wp_run {α} (x : StateT State UB α) (Q : α → State → Prop) (E : EPost.Nil) (s : State) :
    wp x Q E s = match x s with | some (a, s') => Q a s' | none => (⊥ : Prop) := by
  rw [show wp x Q E s = wp (x s) (fun p : α × State => Q p.1 p.2) E from rfl]
  cases hx : x s <;> rfl

/-- `StateT σ UB` interprets `pure`/`bind` exactly (it is a monad morphism). -/
theorem stPureLe {σ α} (a : α) (post : α → σ → Prop) (E : EPost.Nil) :
    wp (pure a : StateT σ UB α) post E ⊑ post a := PartialOrder.rel_refl

theorem stBindLe {σ α β} (x : StateT σ UB α) (f : α → StateT σ UB β) (post : β → σ → Prop)
    (E : EPost.Nil) :
    wp (x >>= f) post E ⊑ wp x (fun a => wp (f a) post E) E := by
  intro s
  exact UB.wp_bind_le (x s) (fun p => f p.1 p.2) (fun p => post p.1 p.2) E

/-- The L2 state refinement, coupled by `couples`. -/
def l2Ref (couples : State → Prop) :
    Refinement (State → Prop) (Heap → Prop) EPost.Nil EPost.Nil where
  γP P := fun s => couples s ∧ P s.heap
  γE := id
  γP_mono h := fun s hs => ⟨hs.1, h s.heap hs.2⟩
  γE_mono h := h

instance (couples : State → Prop) :
    LawfulRefinement (l2Ref couples) (StateT State UB) (StateT Heap UB) :=
  .ofWPMorphism stPureLe stBindLe

/-- `wp` of a `size_t` local read: the result, or `⊥` if the local is missing/wrong-typed. -/
theorem wp_getSize (x : Ident) (Q : USize → State → Prop) (E : EPost.Nil) :
    wp (getSize x) Q E = fun s => match s.locals x with | some (.size n) => Q n s | _ => (⊥ : Prop) := by
  funext s; rw [wp_run]; simp only [getSize]
  cases hl : s.locals x with
  | none => rfl
  | some v => cases v <;> rfl

/-- Reading a coupled `size_t` local extracts to the λ-bound value; the coupling discharges the
projection-UB. -/
theorem corres_getSize (couples : State → Prop) (x : Ident) (v : USize)
    (hx : ∀ s, couples s → s.locals x = some (.size v)) :
    Corres (l2Ref couples) (id : USize → USize) (pure v : StateT Heap UB USize) (getSize x) := by
  intro Q E
  rw [wp_getSize]
  intro s hlhs
  obtain ⟨hcpl, hQ⟩ := hlhs
  rw [hx s hcpl]
  exact ⟨hcpl, hQ⟩

end Zip
