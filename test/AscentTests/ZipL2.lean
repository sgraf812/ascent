import AscentTests.Zip

/-!
# L2 (local-variable extraction): the refinement and the loop body

The concrete state `State` (untyped locals map + heap) is abstracted to just `Heap`, a genuine
data refinement (`γP ≠ id`): an abstract heap-assertion `P` is concretized to
`fun s => couples s.locals ∧ P s.heap`, where `couples` says the locals hold the expected values.
The meet (not implication) is what makes it sound: off the coupling the concretized assertion is
`⊥`, matching the fact that an extracted program makes no claim there.

Reading a coupled local *extracts* to the λ-bound value (`corres_getSize`/`corres_getPtr`); the
heap operations correspond to their heap-only counterparts under a fixed coupling, which they
preserve (`corres_load`/`corres_store`/`corres_cguard`). The loop counter update `setSize "i"`
evolves the coupling, so it belongs to the loop step (`corres_whileLoop`, next).
-/

open Std.Internal.Do Lean.Order Ascent

namespace Zip

/-- `wp` over `StateT σ UB` runs the program and reads off the result. -/
theorem wp_run {σ α} (x : StateT σ UB α) (Q : α → σ → Prop) (E : EPost.Nil) (s : σ) :
    wp x Q E s = match x s with | some (a, s') => Q a s' | none => (⊥ : Prop) := by
  rw [show wp x Q E s = wp (x s) (fun p : α × σ => Q p.1 p.2) E from rfl]
  cases hx : x s <;> rfl

/-- `StateT σ UB` interprets `pure`/`bind` exactly (it is a monad morphism). -/
theorem stPureLe {σ α} (a : α) (post : α → σ → Prop) (E : EPost.Nil) :
    wp (pure a : StateT σ UB α) post E ⊑ post a := PartialOrder.rel_refl

theorem stBindLe {σ α β} (x : StateT σ UB α) (f : α → StateT σ UB β) (post : β → σ → Prop)
    (E : EPost.Nil) :
    wp (x >>= f) post E ⊑ wp x (fun a => wp (f a) post E) E := by
  intro s; exact UB.wp_bind_le (x s) (fun p => f p.1 p.2) (fun p => post p.1 p.2) E

/-- The L2 state refinement, coupled by `couples` on the locals (heap-independent, so heap
operations preserve it). -/
def l2Ref (couples : Locals → Prop) :
    Refinement (State → Prop) (Heap → Prop) EPost.Nil EPost.Nil where
  γP P := fun s => couples s.locals ∧ P s.heap
  γE := id
  γP_mono h := fun s hs => ⟨hs.1, h s.heap hs.2⟩
  γE_mono h := h

instance (couples : Locals → Prop) :
    LawfulRefinement (l2Ref couples) (StateT State UB) (StateT Heap UB) :=
  .ofWPMorphism stPureLe stBindLe

/-! ## Heap-only primitives (the L2 abstract memory operations) -/

def loadH (p : Addr) : StateT Heap UB I := fun h => some (h.data p, h)
def storeH (p : Addr) (v : I) : StateT Heap UB Unit :=
  fun h => some (⟨⟩, { h with data := fun a => if a = p then v else h.data a })
def cguardH (p : Addr) : StateT Heap UB Unit := fun h => if h.valid p then some (⟨⟩, h) else UB.fail

/-! ## Local reads extract to λ-bound values -/

theorem wp_getSize (x : Ident) (Q : USize → State → Prop) (E : EPost.Nil) :
    wp (getSize x) Q E = fun s => match s.locals x with | some (.size n) => Q n s | _ => (⊥ : Prop) := by
  funext s; rw [wp_run]; simp only [getSize]; cases s.locals x with | none => rfl | some v => cases v <;> rfl

theorem wp_getPtr (x : Ident) (Q : Addr → State → Prop) (E : EPost.Nil) :
    wp (getPtr x) Q E = fun s => match s.locals x with | some (.ptr a) => Q a s | _ => (⊥ : Prop) := by
  funext s; rw [wp_run]; simp only [getPtr]; cases s.locals x with | none => rfl | some v => cases v <;> rfl

theorem corres_getSize (couples : Locals → Prop) (x : Ident) (v : USize)
    (hx : ∀ l, couples l → l x = some (.size v)) :
    Corres (l2Ref couples) (id : USize → USize) (pure v : StateT Heap UB USize) (getSize x) := by
  intro Q E
  rw [wp_getSize]
  intro s hlhs
  obtain ⟨hcpl, hQ⟩ := hlhs
  rw [hx s.locals hcpl]
  exact ⟨hcpl, hQ⟩

theorem corres_getPtr (couples : Locals → Prop) (x : Ident) (a : Addr)
    (hx : ∀ l, couples l → l x = some (.ptr a)) :
    Corres (l2Ref couples) (id : Addr → Addr) (pure a : StateT Heap UB Addr) (getPtr x) := by
  intro Q E
  rw [wp_getPtr]
  intro s hlhs
  obtain ⟨hcpl, hQ⟩ := hlhs
  rw [hx s.locals hcpl]
  exact ⟨hcpl, hQ⟩

/-! ## Heap operations correspond to their heap-only counterparts (coupling preserved) -/

theorem corres_load (couples : Locals → Prop) (p : Addr) :
    Corres (l2Ref couples) (id : I → I) (loadH p) (load p) := by
  intro Q E s hs; exact hs

theorem corres_store (couples : Locals → Prop) (p : Addr) (v : I) :
    Corres (l2Ref couples) (id : Unit → Unit) (storeH p v) (store p v) := by
  intro Q E s hs; exact hs

theorem wp_cguardH (p : Addr) (Q : Unit → Heap → Prop) (E : EPost.Nil) :
    wp (cguardH p) Q E = fun h => if h.valid p then Q ⟨⟩ h else (⊥ : Prop) := by
  funext h; rw [wp_run]; by_cases hv : h.valid p <;> simp [cguardH, hv, UB.fail]

theorem wp_cguard (p : Addr) (Q : Unit → State → Prop) (E : EPost.Nil) :
    wp (cguard p) Q E = fun s => if s.heap.valid p then Q ⟨⟩ s else (⊥ : Prop) := by
  funext s; rw [wp_run]; by_cases hv : s.heap.valid p <;> simp [cguard, hv, UB.fail]

theorem corres_cguard (couples : Locals → Prop) (p : Addr) :
    Corres (l2Ref couples) (id : Unit → Unit) (cguardH p) (cguard p) := by
  intro Q E
  rw [wp_cguardH]
  intro s hs
  obtain ⟨hcpl, hq⟩ := hs
  rw [wp_cguard]
  by_cases hv : s.heap.valid p
  · rw [if_pos hv] at hq ⊢; exact ⟨hcpl, hq⟩
  · rw [if_neg hv] at hq ⊢; exact hq

end Zip
