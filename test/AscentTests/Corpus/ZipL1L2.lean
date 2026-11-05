import AscentTests.ZipWithAdd
import Ascent.Tactic.VCGen.Frontend
import Ascent.Refinement.StateRepr

/-!
# Corpus: the L1 → L2 steps of `zip_with_add`

Each entry states a refinement of `ZipWithAdd` with a hole for the abstract program. An entry
that the engine does not yet synthesize asserts the failure with `fail_if_success`, and its
docstring names the gap. When the gap closes, the entry fails and becomes a check of the
synthesized program against the hand-written one.

The `getSize` spec states the presence of the local as a VC `∃ n, s.locals x = some (.size n)`,
and it reads the value as the term `(s.locals x).get!.toSize`. A precondition or a state relation
states the concrete state as an equation `s = { locals := …, heap := h }`. `vcgen` substitutes this
equation, and `simp` then reduces each read value to a variable of the entry.

The other locals `L` and the heap `h` of the equation are parameters of the entry. In C2, the
refinement for all `L` and `h` is equivalent to the refinement under the precondition
`s.locals "len_a" = some (.size la) ∧ s.locals "len_b" = some (.size lb)`.
-/

open Std.WP Lean.Order Ascent Ascent.Concretization Zip

set_option experimental.vcgen true

namespace Zip.Corpus

/-- The locals live in the concrete state only: the abstract state is the heap. -/
abbrev γh : Concretization (State → Prop) (Heap → Prop) := ofStateRepr State.heap

@[ascend high] theorem setSize_stutter {β AV : Type} (x : Ident) (n : USize) (k : Unit → M β)
    (a : StateT Heap UB AV) (Q : β → AV → State → Prop) (E : EStack⟨⟩) :
    (fun s => wp (setSize x n) (fun u s' => s'.heap = s.heap ∧ wrp γh (k u) a Q E s') E s)
      ⊑ wrp γh (setSize x n >>= k) a Q E :=
  wrp_stutter State.heap _ k a Q E

@[ascend high] theorem getSize_stutter {β AV : Type} (x : Ident) (k : USize → M β)
    (a : StateT Heap UB AV) (Q : β → AV → State → Prop) (E : EStack⟨⟩) :
    (fun s => wp (getSize x) (fun v s' => s'.heap = s.heap ∧ wrp γh (k v) a Q E s') E s)
      ⊑ wrp γh (getSize x >>= k) a Q E :=
  wrp_stutter State.heap _ k a Q E

@[ascend] theorem getSize_read (x : Ident) (av : USize) (Q : USize → USize → State → Prop)
    (E : EStack⟨⟩) :
    (fun s => wp (getSize x) (fun v s' => s'.heap = s.heap ∧ Q v av s') E s)
      ⊑ wrp γh (getSize x) (pure av : StateT Heap UB USize) Q E :=
  wrp_read State.heap _ av Q E

@[ascend] theorem getSize_read_rel {Aσ : Type} (J : State → Aσ → Prop) (x : Ident) (av : USize)
    (Q : USize → USize → State → Prop) (E : EStack⟨⟩) :
    (⨅ as, (J · as) ⇨ wp (getSize x) (fun v s' => J s' as ∧ Q v av s') E)
      ⊑ wrp (ofStateRel J) (getSize x) (pure av : StateT Aσ UB USize) Q E :=
  wrp_read_rel J _ av Q E

/-- C1: a write of `"n"` followed by its read. -/
def c1 (v : USize) : { a : StateT Heap UB USize //
    ⦃(⊤ : State → Prop)⦄ (setSize "n" v >>= fun _ => getSize "n") ⪯[γh] a ⦃(⌜· = ·⌝)⦄ } := by
  apply Subtype.mk
  ascend

example (v : USize) : (c1 v).1 = pure v := rfl

/-- C2: the entry prefix of `zipL1`, with `"len_a"` and `"len_b"` given. -/
def c2 (la lb : USize) (L : Locals) (h : Heap) : { a : StateT Heap UB USize //
    ⦃fun s => s = { locals := (fun y => if y = "len_a" then some (.size la)
        else if y = "len_b" then some (.size lb) else L y), heap := h }⦄
      (do
        let la' ← getSize "len_a"
        let lb' ← getSize "len_b"
        setSize "n" (min la' lb')
        setSize "i" 0
        getSize "n")
      ⪯[γh] a ⦃(⌜· = ·⌝)⦄ } := by
  apply Subtype.mk
  ascend

example (la lb : USize) (L : Locals) (h : Heap) : (c2 la lb L h).1 = pure (min la lb) := rfl

/-- The loop relation `invL2`, with the concrete state as an equation. -/
abbrev invL2Eq (a b out : Addr) (n : USize) (L : Locals) : State → USize × Heap → Prop :=
  fun s p =>
    s = { locals := fun y =>
            if y = "i" then some (.size p.1) else if y = "n" then some (.size n)
            else if y = "a" then some (.ptr a) else if y = "b" then some (.ptr b)
            else if y = "out" then some (.ptr out) else L y,
          heap := p.2 }

/-- C3: `refines_getSizeN`, the `return n` of the loop phase under the loop relation. -/
def c3 (a b out : Addr) (n : USize) (L : Locals) : { p : StateT (USize × Heap) UB USize //
    ⦃(⊤ : State → Prop)⦄ (getSize "n") ⪯[ofStateRel (invL2Eq a b out n L)] p ⦃(⌜· = ·⌝)⦄ } := by
  apply Subtype.mk
  ascend

example (a b out : Addr) (n : USize) (L : Locals) : (c3 a b out n L).1 = pure n := rfl

/-! ## Entries that need more than the engine has

* C4: `refines_stepL2`, `stepL1` under `ofStateRel (invL2 a b out n)`. It needs abstract primitives
  on `USize × Heap` (guarded heap access, the counter update) to state the expected program.
* C5: `refines_L1L2`, the loop. It needs the loop rule as a spec (milestone M5).
-/

end Zip.Corpus
