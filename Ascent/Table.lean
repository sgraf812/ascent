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

/-- The cell of `tbl` at `k`, `none` for a key without an entry. -/
def Table.get? {κ β : Type} [DecidableEq κ] (tbl : Table κ β) (k : κ) : Option β :=
  List.lookup k tbl

/-- `tbl` without the entries at `k`. -/
def Table.erase {κ β : Type} [DecidableEq κ] (tbl : Table κ β) (k : κ) : Table κ β :=
  tbl.filter fun e => !(e.1 == k)

section
variable {κ β : Type} [DecidableEq κ]

theorem Table.get?_nil (k : κ) : Table.get? ([] : Table κ β) k = none := rfl

theorem Table.get?_cons (k k' : κ) (b : β) (t : Table κ β) :
    Table.get? ((k', b) :: t) k = if k = k' then some b else Table.get? t k := by
  simp only [Table.get?, List.lookup]
  by_cases h : k = k'
  · simp [h]
  · have hb : (k == k') = false := by simpa using h
    simp [h, hb]

theorem Table.erase_nil (k : κ) : Table.erase ([] : Table κ β) k = [] := rfl

theorem Table.erase_cons (k k' : κ) (b : β) (t : Table κ β) :
    Table.erase ((k', b) :: t) k = if k' = k then Table.erase t k else (k', b) :: Table.erase t k := by
  by_cases h : k' = k <;> simp [Table.erase, h]

theorem Table.get?_erase (t : Table κ β) (h k : κ) :
    Table.get? (Table.erase t h) k = if k = h then none else Table.get? t k := by
  induction t with
  | nil => split <;> rfl
  | cons e t ih =>
    obtain ⟨k', b⟩ := e
    rw [Table.erase_cons]
    by_cases hk : k' = h
    · subst hk
      simp only [↓reduceIte]
      rw [ih, Table.get?_cons]
      by_cases hkk : k = k' <;> simp [hkk]
    · simp only [hk, ↓reduceIte]
      rw [Table.get?_cons, Table.get?_cons, ih]
      by_cases hkk : k = k'
      · subst hkk; simp [hk]
      · simp [hkk]

end

@[vcgen_rintro]
theorem forall_mem_cons_intro {α : Type u} {a : α} {l : List α} {p : α → Prop} (h₁ : p a)
    (h₂ : ∀ x ∈ l, p x) : ∀ x ∈ a :: l, p x :=
  List.forall_mem_cons.mpr ⟨h₁, h₂⟩

@[vcgen_rintro]
theorem forall_mem_nil_intro {α : Type u} {p : α → Prop} : ∀ x ∈ ([] : List α), p x :=
  List.forall_mem_nil p

end Ascent
