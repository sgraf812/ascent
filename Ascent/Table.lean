import Ascent.Refinement
import Lean.Elab.Tactic.VCGen.RIntroAttr

/-!
# Tables

A `Table κ β` is a finite map from keys to cells, built by `ascend` one cell per key: a spec whose
abstract program reads a slot `Table.get tbl k` at a closed key `k` lets the run synthesize the
cell for `k` on its own, and the table collects the cells of all keys.
-/

namespace Ascent

/-- A finite map from keys to cells, as a list of entries. -/
abbrev Table (κ β : Type) := List (κ × β)

/-- The cell of `tbl` at `k`, the default cell for a key without an entry. -/
def Table.get {κ β : Type} [DecidableEq κ] [Inhabited β] (tbl : Table κ β) (k : κ) : β :=
  (List.lookup k tbl).getD default

@[vcgen_rintro]
theorem forall_mem_cons_intro {α : Type u} {a : α} {l : List α} {p : α → Prop} (h₁ : p a)
    (h₂ : ∀ x ∈ l, p x) : ∀ x ∈ a :: l, p x :=
  List.forall_mem_cons.mpr ⟨h₁, h₂⟩

@[vcgen_rintro]
theorem forall_mem_nil_intro {α : Type u} {p : α → Prop} : ∀ x ∈ ([] : List α), p x :=
  List.forall_mem_nil p

end Ascent
