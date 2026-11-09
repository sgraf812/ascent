import Demo.L1

/-!
# Arrays of words in the data memory

`words w b m p n` is the list of the first `n` words of `w` bytes of the array at `p`, each read as a
`b`-bit vector. After `k`
iterations of the loop of `zipWithAdd` the memory is `stores m A B O k`: the first `k` cells of
`O` hold `word 8 64 m A j + word 8 64 m B j`, read in the memory before the loop, and every other cell of the
inputs, the output and the return slot is as it was. The lemmas on the branch conditions decide the
tests of the loop on a length below `2 ^ 61`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken

namespace Ascent.Kraken

/-! ## Arrays of words -/

/-- The address of the `w`-byte word at index `k` of the array at `p`. -/
def cell (w : Nat) (p : BitVec 64) (k : Nat) : BitVec 64 := p + BitVec.ofNat 64 k * BitVec.ofNat 64 w

/-- The `w`-byte word at index `k` of the array at `p`, as a `b`-bit vector. -/
def word (w b : Nat) (m : DataMem) (p : BitVec 64) (k : Nat) : BitVec b :=
  BitVec.ofInt b (Mem.loadInt m (cell w p k) w).get!

/-- The first `n` words of `w` bytes of the array at `p`. -/
def words (w b : Nat) (m : DataMem) (p : BitVec 64) (n : Nat) : List (BitVec b) :=
  List.ofFn fun k : Fin n => word w b m p k

theorem toNat_offset {w k : Nat} (hw : w ≤ 8) (hk : k < 2 ^ 61) :
    (BitVec.ofNat 64 k * BitVec.ofNat 64 w).toNat = w * k := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : w * k < 2 ^ 64 := by
    calc w * k ≤ 8 * k := Nat.mul_le_mul_right k hw
      _ < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : w < 2 ^ 64),
    Nat.mul_comm, Nat.mod_eq_of_lt this]

theorem cell_inside {w : Nat} {p : BitVec 64} {k n : Nat} (hw : w ≤ 8) (hk : k < n) (hn : n < 2 ^ 61) :
    Mem.Blocks.Inside (cell w p k) w [(p, w * n)] :=
  Mem.Blocks.Inside.base_add (by
    rw [toNat_offset hw (by omega)]
    have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hk)
    rw [Nat.mul_succ] at this
    omega)

theorem cell_disjoint {w : Nat} {p : BitVec 64} {j k n : Nat} (hw : w ≤ 8) (hj : j < n) (hk : k < n)
    (hjk : j ≠ k) (hn : n < 2 ^ 61) : Mem.Blocks.Disjoint [(cell w p j, w)] [(cell w p k, w)] := by
  have hsub : ∀ x y : BitVec 64, p + x - (p + y) = x - y := fun x y => by grind
  unfold cell
  have hjw := toNat_offset (w := w) (k := j) hw (by omega)
  have hkw := toNat_offset (w := w) (k := k) hw (by omega)
  have h1 : w * j < 2 ^ 64 := by
    calc w * j ≤ 8 * j := Nat.mul_le_mul_right j hw
      _ < 2 ^ 64 := by omega
  have h2 : w * k < 2 ^ 64 := by
    calc w * k ≤ 8 * k := Nat.mul_le_mul_right k hw
      _ < 2 ^ 64 := by omega
  have h1' : w * j + w ≤ 2 ^ 64 := by
    rw [← Nat.mul_succ]
    calc w * j.succ ≤ 8 * j.succ := Nat.mul_le_mul_right _ hw
      _ ≤ 2 ^ 64 := by omega
  have h2' : w * k + w ≤ 2 ^ 64 := by
    rw [← Nat.mul_succ]
    calc w * k.succ ≤ 8 * k.succ := Nat.mul_le_mul_right _ hw
      _ ≤ 2 ^ 64 := by omega
  rcases Nat.lt_or_gt_of_ne hjk with h | h
  · have : w * j + w ≤ w * k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left w h
    refine Mem.Blocks.Disjoint.of_sub ?_ ?_ <;> rw [hsub, BitVec.toNat_sub, hjw, hkw] <;> omega
  · have : w * k + w ≤ w * j := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left w h
    refine Mem.Blocks.Disjoint.of_sub ?_ ?_ <;> rw [hsub, BitVec.toNat_sub, hjw, hkw] <;> omega

/-! ## The memory after `k` iterations -/

/-- The memory after `k` iterations: cell `j < k` of `O` holds `word 8 64 m A j + word 8 64 m B j`. -/
def stores (m : DataMem) (A B O : BitVec 64) : Nat → DataMem
  | 0 => m
  | k + 1 => Mem.storeInt (stores m A B O k) (cell 8 O k) 8 (word 8 64 m A k + word 8 64 m B k).toInt

section
variable {m : DataMem} {A B O : BitVec 64} {n : Nat}

theorem stores_mapped {bs : List (BitVec 64 × Nat)} (h : Mem.Mapped bs m) :
    ∀ k, Mem.Mapped bs (stores m A B O k)
  | 0 => h
  | k + 1 => Mem.Mapped.storeInt (stores_mapped h k) _ _ _

theorem loadInt_stores_of_disjoint {x : BitVec 64} :
    ∀ k, (∀ j < k, Mem.Blocks.Disjoint [(x, 8)] [(cell 8 O j, 8)]) →
      Mem.loadInt (stores m A B O k) x 8 = Mem.loadInt m x 8
  | 0, _ => rfl
  | k + 1, h => by
    rw [stores, Mem.loadInt_storeInt_of_disjoint (h k (Nat.lt_succ_self k)) _]
    exact loadInt_stores_of_disjoint k fun j hj => h j (Nat.lt_succ_of_lt hj)

theorem word_stores_of_disjoint {p : BitVec 64} (hd : Mem.Blocks.Disjoint [(O, 8 * n)] [(p, 8 * n)])
    (hn : n < 2 ^ 61) {j k : Nat} (hj : j < n) (hk : k ≤ n) :
    word 8 64 (stores m A B O k) p j = word 8 64 m p j := by
  unfold word
  rw [loadInt_stores_of_disjoint k fun i hi =>
    Mem.Blocks.Disjoint.of_inside' hd (cell_inside (by omega) hj hn) (cell_inside (by omega) (by omega) hn)]

theorem word_stores_out (hn : n < 2 ^ 61) :
    ∀ {k j : Nat}, k ≤ n → j < k → word 8 64 (stores m A B O k) O j = word 8 64 m A j + word 8 64 m B j
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, j, hk, hj => by
    by_cases hjk : j = k
    · subst hjk
      unfold word
      rw [stores, Mem.loadInt_storeInt _ _ _ _ (by decide), Option.get!_some,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt]
      rfl
    · unfold word
      rw [stores, Mem.loadInt_storeInt_of_disjoint
        (cell_disjoint (by omega) (by omega) (by omega) hjk hn) _]
      exact word_stores_out hn (by omega) (by omega)

theorem words_stores_out (hn : n < 2 ^ 61) :
    words 8 64 (stores m A B O n) O n = List.zipWith (· + ·) (words 8 64 m A n) (words 8 64 m B n) := by
  apply List.ext_getElem
  · simp [words]
  · intro j h₁ h₂
    simp only [words, List.getElem_ofFn, List.getElem_zipWith]
    simp only [words, List.length_ofFn] at h₁
    exact word_stores_out hn (Nat.le_refl n) h₁

end

end Ascent.Kraken
