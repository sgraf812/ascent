import Demo.L2

/-!
# What `zipWithAdd` computes

`zipWithAddR_spec` states the result of the second layer: from a state in which `rdi`, `rsi` and
`rdx` point to arrays `A`, `B` and `O` of `n` words and `rcx` holds `n`, the program returns with
`words m' O n = List.zipWith (· + ·) (words m A n) (words m B n)`. The output array is apart from
the inputs and from the return slot.

After `k` iterations of the loop the memory is `stores m A B O k`: the first `k` cells of `O` hold
the sums, read in the memory before the loop.
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

theorem cmp_le_self_zero : CondCode.cmp .le (BitVec.ofNat 64 0 &&& BitVec.ofNat 64 0) 0 = true := by
  decide

theorem cmp_nz_succ {k n : Nat} (hk : k < n) (hn : n < 2 ^ 61) :
    CondCode.cmp .nz (BitVec.ofNat 64 n) (BitVec.ofNat 64 k + 1) = decide (k + 1 ≠ n) := by
  simp only [CondCode.cmp]
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, ne_eq, BitVec.toNat_eq,
    BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem toNat_ofNat_succ {k : Nat} (hk : k < 2 ^ 61) : (BitVec.ofNat 64 k + 1).toNat = k + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem toNat_ofNat_lt {k : Nat} (hk : k < 2 ^ 61) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat]; omega

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.ofNat_add]; rfl

/-! ## The specification -/

/-- The state at the entry of `zipWithAdd`: `rdi`, `rsi` and `rdx` point to arrays `A`, `B` and `O`
of `n` mapped words, `rcx` holds `n`, the output array is apart from the inputs and from the return
slot, and the return slot is mapped. -/
structure ZipWithAddPre (st : RegMem) (A B O : BitVec 64) (n : Nat) : Prop where
  rdi : st.regs .rdi = A
  rsi : st.regs .rsi = B
  rdx : st.regs .rdx = O
  rcx : st.regs .rcx = BitVec.ofNat 64 n
  len : n < 2 ^ 61
  mapA : Mem.Mapped [(A, 8 * n)] st.mem
  mapB : Mem.Mapped [(B, 8 * n)] st.mem
  mapO : Mem.Mapped [(O, 8 * n)] st.mem
  disjA : Mem.Blocks.Disjoint [(O, 8 * n)] [(A, 8 * n)]
  disjB : Mem.Blocks.Disjoint [(O, 8 * n)] [(B, 8 * n)]
  disjR : Mem.Blocks.Disjoint [(st.regs .rsp, 8)] [(O, 8 * n)]
  ret : (Mem.loadInt st.mem (st.regs .rsp) 8).isSome = true

/-- The registers the loop reads and never writes. -/
def SameArgs (st st₀ : RegMem) : Prop :=
  st.regs .rdi = st₀.regs .rdi ∧ st.regs .rsi = st₀.regs .rsi ∧ st.regs .rdx = st₀.regs .rdx
    ∧ st.regs .rcx = st₀.regs .rcx ∧ st.regs .rsp = st₀.regs .rsp

/-- The invariant at each label. At `LBB0_2`, `rax` holds the index `k` of the next iteration. -/
def zipInv (st₀ : RegMem) (A B O : BitVec 64) (n : Nat) (l : CfgLabel) (st : RegMem) : Prop :=
  if l = .entry then st = st₀
  else if l = .label "LBB0_2" then
    ∃ k, k < n ∧ st.regs .rax = BitVec.ofNat 64 k ∧ SameArgs st st₀ ∧ st.mem = stores st₀.mem A B O k
  else if l = .label "LBB0_3" then
    st.regs .rsp = st₀.regs .rsp ∧ st.mem = stores st₀.mem A B O n
  else False

/-- The number of blocks the run can still take before `LBB0_3`. -/
def zipVar (n : Nat) (l : CfgLabel) (st : RegMem) : Nat :=
  if l = .entry then n + 2
  else if l = .label "LBB0_2" then n - (st.regs .rax).toNat + 1
  else 0

/-- The result of the run: the return address leaves the stack, and the output array holds the
sums of the inputs. -/
def ZipWithAddPost (st₀ : RegMem) (A B O : BitVec 64) (n : Nat) (st : RegMem) : Prop :=
  st.regs .rsp = st₀.regs .rsp + 8
    ∧ words st.mem O n = List.zipWith (· + ·) (words st₀.mem A n) (words st₀.mem B n)

section
variable [Host] [FunDecls] [Embeds zipWithAdd]

theorem zipWithAddR_spec (s : MachineData) (ra : Int64) {st₀ : RegMem} {A B O : BitVec 64} {n : Nat}
    (h : ZipWithAddPre st₀ A B O n) :
    wp (zipWithAddR s ra) (fun _ _ => False)
      (fun l st => l = .exit ∧ ZipWithAddPost st₀ A B O n st, estack⟨⟩) st₀ := by
  have hlen := h.len
  have hnext₀ : Program.next zipWithAdd .entry = .label "LBB0_2" := rfl
  have hnext₂ : Program.next zipWithAdd (.label "LBB0_2") = .label "LBB0_3" := rfl
  unfold zipWithAddR
  refine wp_cfgLoop_of_inv _ _ _ _ (zipInv st₀ A B O n) (zipVar n) ?_ ?_ .entry st₀
    (by simp [zipInv])
  · intro st hI
    simp [zipInv] at hI
  · intro l st hl hI
    by_cases h₀ : l = .entry
    · -- the entry block
      subst h₀
      simp only [zipInv, ↓reduceIte] at hI
      subst hI
      simp only [Table.get, List.lookup, BEq.rfl, Option.getD_some, hnext₀,
        WPMonadExact.wp_bind_eq, WPMonadExact.wp_pure_eq, RInstr.testJcc, RInstr.xorReg32Reg32,
        AInstr.wp_branch, AInstr.wp_modifyIf]
      rw [h.rcx]
      by_cases hn0 : n = 0
      · subst hn0
        rw [cmp_le_self_zero]
        simp [zipInv, zipVar, stores]
      · rw [cmp_le_self_of_pos (Nat.pos_of_ne_zero hn0) hlen]
        simp only [Bool.false_eq_true, ↓reduceIte, true_and]
        refine ⟨?_, fun _ => ?_⟩
        · simp only [zipInv, reduceCtorEq, ↓reduceIte, RegMem.set_regs, RegMem.set_mem]
          refine ⟨0, Nat.pos_of_ne_zero hn0, by simp, ?_, rfl⟩
          simp [SameArgs]
        · simp only [zipVar, reduceCtorEq, ↓reduceIte, RegMem.set_regs]
          simp
    by_cases h₂ : l = .label "LBB0_2"
    · -- the loop block
      subst h₂
      simp only [zipInv, reduceCtorEq, ↓reduceIte] at hI
      obtain ⟨k, hk, hrax, hsame, hmem⟩ := hI
      obtain ⟨hrdi, hrsi, hrdx, hrcx, hrsp⟩ := hsame
      have hcell : ∀ p : BitVec 64, p + BitVec.ofNat 64 k * 8 + BitVec.ofInt 64 (Int64.toInt 0)
          = cell p k := fun p => by simp [cell]
      have hb₁ : (CfgLabel.label "LBB0_2" == CfgLabel.entry) = false := rfl
      have hb₂ : (CfgLabel.label "LBB0_2" == CfgLabel.label "LBB0_2") = true := rfl
      simp only [Table.get, List.lookup, hb₁, hb₂, Option.getD_some, hnext₂,
        WPMonadExact.wp_bind_eq, WPMonadExact.wp_pure_eq,
        RInstr.movRegSib8, RInstr.addRegSib8, RInstr.movSib8Reg, RInstr.incReg, RInstr.cmpJcc,
        AInstr.wp_branch, AInstr.wp_modifyIf, RegMem.set_regs, RegMem.set_mem, reduceCtorEq,
        ↓reduceIte, hrsi, hrdi, hrdx, hrcx, hrsp, hrax, h.rsi, h.rdi, h.rdx, h.rcx, hcell, hmem]
      have hwA : BitVec.ofInt 64 (Mem.loadInt (stores st₀.mem A B O k) (cell A k) 8).get!
          = word st₀.mem A k := word_stores_of_disjoint h.disjA hlen hk (Nat.le_of_lt hk)
      have hwB : BitVec.ofInt 64 (Mem.loadInt (stores st₀.mem A B O k) (cell B k) 8).get!
          = word st₀.mem B k := word_stores_of_disjoint h.disjB hlen hk (Nat.le_of_lt hk)
      have hst : Mem.storeInt (stores st₀.mem A B O k) (cell O k) 8
          (word st₀.mem A k + word st₀.mem B k).toInt = stores st₀.mem A B O (k + 1) := rfl
      rw [hwA, hwB, hst, cmp_nz_succ hk hlen]
      refine ⟨Mem.Mapped.loadInt_isSome (stores_mapped h.mapB k) (cell_inside hk hlen),
        Mem.Mapped.loadInt_isSome (stores_mapped h.mapA k) (cell_inside hk hlen),
        ⟨Mem.Mapped.loadInt_isSome (stores_mapped h.mapO k) (cell_inside hk hlen),
          Mem.Blocks.Disjoint.of_inside_right_pair h.disjR (cell_inside hk hlen)⟩, trivial, ?_⟩
      by_cases hkn : k + 1 = n
      · simp only [hkn, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        simp [zipInv, zipVar, hrsp]
      · simp only [hkn, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · simp only [zipInv, reduceCtorEq, ↓reduceIte, RegMem.set_regs, RegMem.set_mem]
          refine ⟨k + 1, by omega, ofNat_succ k, ?_, rfl⟩
          simp [SameArgs, hrdi, hrsi, hrdx, hrcx, hrsp]
        · simp only [zipVar, reduceCtorEq, ↓reduceIte, RegMem.set_regs]
          rw [toNat_ofNat_succ (by omega), hrax, toNat_ofNat_lt (by omega)]
          omega
    by_cases h₃ : l = .label "LBB0_3"
    · -- the return block
      subst h₃
      simp [zipInv] at hI
      obtain ⟨hrsp, hmem⟩ := hI
      have hb₁ : (CfgLabel.label "LBB0_3" == CfgLabel.entry) = false := rfl
      have hb₂ : (CfgLabel.label "LBB0_3" == CfgLabel.label "LBB0_2") = false := rfl
      have hb₃ : (CfgLabel.label "LBB0_3" == CfgLabel.label "LBB0_3") = true := rfl
      have hslot : Mem.loadInt (stores st₀.mem A B O n) (st₀.regs .rsp) 8
          = Mem.loadInt st₀.mem (st₀.regs .rsp) 8 :=
        loadInt_stores_of_disjoint n fun j hj =>
          Mem.Blocks.Disjoint.of_inside_right_pair h.disjR (cell_inside hj hlen)
      simp only [Table.get, List.lookup, hb₁, hb₂, hb₃, Option.getD_some, RInstr.ret,
        AInstr.wp_exitIf, ↓reduceIte, hrsp]
      refine ⟨by rw [hmem, hslot]; exact h.ret, trivial, by simp, ?_⟩
      rw [RegMem.set_mem, hmem]
      exact words_stores_out hlen
    · simp [zipInv, h₀, h₂, h₃] at hI

end

end Ascent.Kraken
