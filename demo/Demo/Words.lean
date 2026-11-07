import Demo.L1

/-!
# Arrays of words in the data memory

`words m p n` is the list of the first `n` eight-byte words of the array at `p`. After `k`
iterations of the loop of `zipWithAdd` the memory is `stores m A B O k`: the first `k` cells of
`O` hold `word m A j + word m B j`, read in the memory before the loop, and every other cell of the
inputs, the output and the return slot is as it was. The lemmas on the branch conditions read the
condition codes of `test` and `cmp` on a length below `2 ^ 61`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken

namespace Ascent.Kraken

/-! ## Arrays of words -/

/-- The address of the word at index `k` of the array at `p`. -/
def cell (p : BitVec 64) (k : Nat) : BitVec 64 := p + BitVec.ofNat 64 k * 8

/-- The word at index `k` of the array at `p`. -/
def word (m : DataMem) (p : BitVec 64) (k : Nat) : BitVec 64 :=
  BitVec.ofInt 64 (Mem.loadInt m (cell p k) 8).get!

/-- The first `n` words of the array at `p`. -/
def words (m : DataMem) (p : BitVec 64) (n : Nat) : List (BitVec 64) :=
  List.ofFn fun k : Fin n => word m p k

theorem toNat_offset {k : Nat} (hk : k < 2 ^ 61) : (BitVec.ofNat 64 k * 8).toNat = 8 * k := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp only [show (8 : BitVec 64).toNat = 8 from rfl]
  omega

theorem cell_inside {p : BitVec 64} {k n : Nat} (hk : k < n) (hn : n < 2 ^ 61) :
    Mem.Blocks.Inside (cell p k) 8 [(p, 8 * n)] :=
  Mem.Blocks.Inside.base_add (by rw [toNat_offset (by omega)]; omega)

theorem cell_disjoint {p : BitVec 64} {j k n : Nat} (hj : j < n) (hk : k < n) (hjk : j ≠ k)
    (hn : n < 2 ^ 61) : Mem.Blocks.Disjoint [(cell p j, 8)] [(cell p k, 8)] := by
  have hsub : ∀ x y : BitVec 64, p + x - (p + y) = x - y := fun x y => by grind
  unfold cell
  have hj8 := toNat_offset (k := j) (by omega)
  have hk8 := toNat_offset (k := k) (by omega)
  refine Mem.Blocks.Disjoint.of_sub ?_ ?_ <;> rw [hsub, BitVec.toNat_sub] <;> omega

/-! ## The memory after `k` iterations -/

/-- The memory after `k` iterations: cell `j < k` of `O` holds `word m A j + word m B j`. -/
def stores (m : DataMem) (A B O : BitVec 64) : Nat → DataMem
  | 0 => m
  | k + 1 => Mem.storeInt (stores m A B O k) (cell O k) 8 (word m A k + word m B k).toInt

section
variable {m : DataMem} {A B O : BitVec 64} {n : Nat}

theorem stores_mapped {bs : List (BitVec 64 × Nat)} (h : Mem.Mapped bs m) :
    ∀ k, Mem.Mapped bs (stores m A B O k)
  | 0 => h
  | k + 1 => Mem.Mapped.storeInt (stores_mapped h k) _ _ _

theorem loadInt_stores_of_disjoint {x : BitVec 64} :
    ∀ k, (∀ j < k, Mem.Blocks.Disjoint [(x, 8)] [(cell O j, 8)]) →
      Mem.loadInt (stores m A B O k) x 8 = Mem.loadInt m x 8
  | 0, _ => rfl
  | k + 1, h => by
    rw [stores, Mem.loadInt_storeInt_of_disjoint (h k (Nat.lt_succ_self k)) _]
    exact loadInt_stores_of_disjoint k fun j hj => h j (Nat.lt_succ_of_lt hj)

theorem word_stores_of_disjoint {p : BitVec 64} (hd : Mem.Blocks.Disjoint [(O, 8 * n)] [(p, 8 * n)])
    (hn : n < 2 ^ 61) {j k : Nat} (hj : j < n) (hk : k ≤ n) :
    word (stores m A B O k) p j = word m p j := by
  unfold word
  rw [loadInt_stores_of_disjoint k fun i hi =>
    Mem.Blocks.Disjoint.of_inside' hd (cell_inside hj hn) (cell_inside (by omega) hn)]

theorem word_stores_out (hn : n < 2 ^ 61) :
    ∀ {k j : Nat}, k ≤ n → j < k → word (stores m A B O k) O j = word m A j + word m B j
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
        (cell_disjoint (by omega) (by omega) hjk hn) _]
      exact word_stores_out hn (by omega) (by omega)

theorem words_stores_out (hn : n < 2 ^ 61) :
    words (stores m A B O n) O n = List.zipWith (· + ·) (words m A n) (words m B n) := by
  apply List.ext_getElem
  · simp [words]
  · intro j h₁ h₂
    simp only [words, List.getElem_ofFn, List.getElem_zipWith]
    simp only [words, List.length_ofFn] at h₁
    exact word_stores_out hn (Nat.le_refl n) h₁

end

/-! ## The branch conditions -/

theorem cmp_le_self_of_pos {n : Nat} (h0 : 0 < n) (hn : n < 2 ^ 61) :
    CondCode.cmp .le (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n) 0 = false := by
  simp only [CondCode.cmp, BitVec.and_self, BitVec.sle_eq_decide, decide_eq_false_iff_not]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  split <;> simp <;> omega

theorem cmp_le_self_zero : CondCode.cmp .le (BitVec.ofNat 64 0 &&& BitVec.ofNat 64 0) 0 = true :=
  rfl

theorem cmp_le_self_eq {n : Nat} (hn : n < 2 ^ 61) :
    CondCode.cmp .le (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n) 0#64 = decide (n = 0) := by
  by_cases h0 : n = 0
  · subst h0; simp only [decide_true]; exact cmp_le_self_zero
  · simp only [h0, decide_false]; exact cmp_le_self_of_pos (Nat.pos_of_ne_zero h0) hn

theorem pos_of_not_cmp_le_self {n : Nat} (hn : n < 2 ^ 61)
    (h : ¬CondCode.cmp .le (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n) 0#64 = true) : 0 < n := by
  rw [cmp_le_self_eq hn, decide_eq_true_iff] at h
  omega

theorem toNat_add_one {v : BitVec 64} (hv : v.toNat < 2 ^ 61) :
    (v + 1#64).toNat = v.toNat + 1 := by
  rw [BitVec.toNat_add]
  simp only [show (1#64 : BitVec 64).toNat = 1 from rfl]
  omega

theorem cmp_nz_add_one {n : Nat} {v : BitVec 64} (hv : v.toNat < n) (hn : n < 2 ^ 61) :
    CondCode.cmp .nz (BitVec.ofNat 64 n) (v + 1#64) = decide (v.toNat + 1 ≠ n) := by
  simp only [CondCode.cmp]
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, ne_eq, BitVec.toNat_eq,
    toNat_add_one (by omega), BitVec.toNat_ofNat]
  omega

theorem toNat_add_one_of_cmp_nz {n : Nat} {v : BitVec 64} (hv : v.toNat < n) (hn : n < 2 ^ 61)
    (_ : CondCode.cmp .nz (BitVec.ofNat 64 n) (v + 1#64) = true) :
    (v + 1#64).toNat = v.toNat + 1 :=
  toNat_add_one (by omega)

theorem toNat_succ_lt_of_cmp_nz {n : Nat} {v : BitVec 64} (hv : v.toNat < n) (hn : n < 2 ^ 61)
    (h : CondCode.cmp .nz (BitVec.ofNat 64 n) (v + 1#64) = true) : (v + 1#64).toNat < n := by
  rw [cmp_nz_add_one hv hn, decide_eq_true_iff] at h
  rw [toNat_add_one (by omega)]
  omega

theorem toNat_add_one_eq_of_not_cmp_nz {n : Nat} {v : BitVec 64} (hv : v.toNat < n)
    (hn : n < 2 ^ 61) (h : ¬CondCode.cmp .nz (BitVec.ofNat 64 n) (v + 1#64) = true) :
    v.toNat + 1 = n := by
  rw [cmp_nz_add_one hv hn, decide_eq_true_iff] at h
  omega

attribute [grind →] pos_of_not_cmp_le_self toNat_add_one_of_cmp_nz toNat_succ_lt_of_cmp_nz
  toNat_add_one_eq_of_not_cmp_nz

end Ascent.Kraken
