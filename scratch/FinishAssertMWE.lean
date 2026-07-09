/-!
# MWE: `grind` closes a heap-congruence goal order-sensitively

Extracted from the `corres_stepL2` loop-body VC in `test/AscentTests/ZipWithAdd.lean`. Proving the
loop invariant on the post-state reduces to a heap equality
`upd heap (n1 + a2) (heap (n1 + a1)) = upd h (out + i) (h (a + i))`, given `heap = h` and the read
facts that pin `n1 = i`, `a1 = a`, `a2 = out` through constructor injectivity.

The three theorems below are the SAME goal under alpha-renaming, differing only in the order of the
bound variables (and one `subst`). `grind` closes it in one order and fails in another. So this is a
`grind` heuristic-incompleteness / order-sensitivity issue, NOT a `vcgen`/`finish` defect: `mkFinish`
already runs `intros 0 >> assertAll`, and sym-mode `finish` behaves identically to default-mode
`grind` on the VC leaf (both assert the framed precondition, both fail in the order `vcgen` produces).
The reliable fix in the development is to `subst` the framed heap before `grind`.
-/

def upd (h : Nat → Nat) (p v : Nat) : Nat → Nat := fun k => if k = p then v else h k

inductive Value | size (n : Nat) | ptr (a : Nat)

/-- **FAILS.** Bound-variable order `n1 a1 a2`. `grind` does not close the goal, though every fact it
needs is asserted (`heap = h`, and `n1 = i` / `a1 = a` / `a2 = out` by injectivity). -/
theorem fails (a out i n1 a1 a2 : Nat) (heap h : Nat → Nat) (loc : String → Option Value)
    (hh : heap = h)
    (hi : loc "i" = some (.size i)) (hi' : loc "i" = some (.size n1))
    (ha : loc "a" = some (.ptr a)) (ha' : loc "a" = some (.ptr a1))
    (ho : loc "out" = some (.ptr out)) (ho' : loc "out" = some (.ptr a2)) :
    upd heap (n1 + a2) (heap (n1 + a1)) = upd h (out + i) (h (a + i)) := by
  grind [upd]

/-- **SUCCEEDS.** The identical goal with the bound variables reordered to `a1 a2 n1`. Only the binder
order changed, yet `grind` now closes it. -/
theorem reorder_closes (a out i a1 a2 n1 : Nat) (heap h : Nat → Nat) (loc : String → Option Value)
    (hh : heap = h)
    (hi : loc "i" = some (.size i)) (hi' : loc "i" = some (.size n1))
    (ha : loc "a" = some (.ptr a)) (ha' : loc "a" = some (.ptr a1))
    (ho : loc "out" = some (.ptr out)) (ho' : loc "out" = some (.ptr a2)) :
    upd heap (n1 + a2) (heap (n1 + a1)) = upd h (out + i) (h (a + i)) := by
  grind [upd]

/-- **SUCCEEDS in any order.** Eliminating `h` via the framed equation first makes `grind` robust; this
is the idiom used in `corres_stepL2` (`obtain ⟨rfl, …⟩; grind`). -/
theorem subst_closes (a out i n1 a1 a2 : Nat) (heap h : Nat → Nat) (loc : String → Option Value)
    (hh : heap = h)
    (hi : loc "i" = some (.size i)) (hi' : loc "i" = some (.size n1))
    (ha : loc "a" = some (.ptr a)) (ha' : loc "a" = some (.ptr a1))
    (ho : loc "out" = some (.ptr out)) (ho' : loc "out" = some (.ptr a2)) :
    upd heap (n1 + a2) (heap (n1 + a1)) = upd h (out + i) (h (a + i)) := by
  subst h
  grind [upd]
