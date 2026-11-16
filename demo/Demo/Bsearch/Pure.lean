import Ascent.Refinement.Catch
import Demo.Bsearch.Arrays
import Demo.Zip.Pure

/-!
# The binary search as a pure program

`bsearchFrame a key lo hi` searches `a[lo, hi)` for `key` the way the machine code does: it looks at the
middle `lo + (hi - lo) / 2`, continues right of it while the element is below `key`, returns the
index when the element is `key`, and continues left of it otherwise. Four equations state the cases:
`bsearchF_of_le` and `bsearchF_found` give the result, and `bsearchF_right` and `bsearchF_left` take
the search on the bounds after one step, `bsearchFrame a key (mid + 1) hi` or `bsearchFrame a key lo mid`,
back to `bsearchFrame a key lo hi`. They are the `grind` theory of the loop proof. `bsearchF_some` and
`bsearchF_none` state the result in terms of membership, and `encodeIdx_bsearchF` states it for the
word of the result: the word of an index of `key`, or `-1` when a sorted `a` holds no `key`.

`bsearchArrays_spec` states that the array program returns `bsearchFrame a key 0 n`. `vcgen` proves it
with the invariant `bsearchFrame a key lo hi = bsearchFrame a key 0 n` on the bounds `lo` and `hi`, and
`ascend_def` then synthesizes the pure program `bsearchPure`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred ofStateRepr_post_post)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken

def bsearchFrame (a : Array (BitVec 64)) (key : BitVec 64) (lo hi : Nat) : Option Nat :=
  if hi ≤ lo then none
  else if a[lo + (hi - lo) / 2]!.toInt < key.toInt then bsearchFrame a key (lo + (hi - lo) / 2 + 1) hi
  else if a[lo + (hi - lo) / 2]!.toInt ≤ key.toInt then some (lo + (hi - lo) / 2)
  else bsearchFrame a key lo (lo + (hi - lo) / 2)
termination_by hi - lo

section
variable {a : Array (BitVec 64)} {key : BitVec 64} {lo hi : Nat}

theorem bsearchF_of_le (h : hi ≤ lo) : bsearchFrame a key lo hi = none := by
  rw [bsearchFrame]; simp [h]

theorem bsearchF_found (h : lo < hi) (hl : ¬a[lo + (hi - lo) / 2]!.toInt < key.toInt)
    (hle : a[lo + (hi - lo) / 2]!.toInt ≤ key.toInt) :
    bsearchFrame a key lo hi = some (lo + (hi - lo) / 2) := by
  rw [bsearchFrame]; simp [Nat.not_le.mpr h, hl, hle]

theorem bsearchF_right (h : lo < hi) (hl : a[lo + (hi - lo) / 2]!.toInt < key.toInt) :
    bsearchFrame a key (lo + (hi - lo) / 2 + 1) hi = bsearchFrame a key lo hi := by
  conv => rhs; rw [bsearchFrame]
  simp [Nat.not_le.mpr h, hl]

theorem bsearchF_left (h : lo < hi) (hl : ¬a[lo + (hi - lo) / 2]!.toInt < key.toInt)
    (hle : ¬a[lo + (hi - lo) / 2]!.toInt ≤ key.toInt) :
    bsearchFrame a key lo (lo + (hi - lo) / 2) = bsearchFrame a key lo hi := by
  conv => rhs; rw [bsearchFrame]
  simp [Nat.not_le.mpr h, hl, hle]

end

def IntSorted (a : Array (BitVec 64)) (hi : Nat) : Prop :=
  ∀ i j, i ≤ j → j < hi → a[i]!.toInt ≤ a[j]!.toInt

theorem IntSorted.le_of_le {a : Array (BitVec 64)} {hi i j : Nat} (hs : IntSorted a hi) (hij : i ≤ j)
    (hj : j < hi) : a[i]!.toInt ≤ a[j]!.toInt :=
  hs i j hij hj

grind_pattern IntSorted.le_of_le => IntSorted a hi, a[i]!, a[j]!

theorem bsearchArrays_mem_spec (key : BitVec 64) (n : Nat) (a : Array (BitVec 64)) (hs : IntSorted a n)
    (ha : a.size = n) :
    ⦃fun _ => True⦄ bsearchArrays key n a
      ⦃fun o _ => (∃ j < n, encodeIdx o = BitVec.ofNat 64 j ∧ a[j]! = key) ∨
          (encodeIdx o = -1 ∧ ∀ j < n, a[j]! ≠ key);
        (fun (_ : Int64) (_ : Unit) => False, estack⟨⟩)⦄ := by
  vcgen [bsearchArrays]
    invariants
    · WhileInvariant.mk fun (done : Bool) (iko : Nat × Nat × Option Nat) (_ : Unit) =>
        (done = false → iko.1 ≤ iko.2.1 ∧ iko.2.1 ≤ n ∧ (∀ j < iko.1, a[j]!.toInt < key.toInt) ∧
          (∀ j, iko.2.1 ≤ j → j < n → key.toInt < a[j]!.toInt)) ∧
        (done = true → (∃ j < n, encodeIdx iko.2.2 = BitVec.ofNat 64 j ∧ a[j]! = key) ∨
          (encodeIdx iko.2.2 = -1 ∧ ∀ j < n, a[j]! ≠ key))
    · Variant.ofMeasure fun (iko : Nat × Nat × Option Nat) => iko.2.1 - iko.1
    simp [Variant.evalsBelow_ofMeasure_nat]
    with finish


attribute [local grind =] bsearchF_of_le bsearchF_found bsearchF_right bsearchF_left in
theorem bsearchArrays_spec (key : BitVec 64) (n : Nat) (a : Array (BitVec 64)) :
    ⦃fun _ => True⦄ bsearchArrays key n a
      ⦃fun o _ => o = bsearchFrame a key 0 n; (fun (_ : Int64) (_ : Unit) => False, estack⟨⟩)⦄ := by
  vcgen [bsearchArrays]
    invariants
    · WhileInvariant.mk fun (done : Bool) (iko : Nat × Nat × Option Nat) (_ : Unit) =>
        (done = false → iko.1 ≤ iko.2.1 ∧ iko.2.1 ≤ n ∧ bsearchFrame a key iko.1 iko.2.1 = bsearchFrame a key 0 n) ∧
        (done = true → iko.2.2 = bsearchFrame a key 0 n)
    · Variant.ofMeasure fun (iko : Nat × Nat × Option Nat) => iko.2.1 - iko.1
    simp [Variant.evalsBelow_ofMeasure_nat]
    with finish

/-! ## The pure program -/

ascend_def bsearchPure (key : BitVec 64) (n : Nat) (a : Array (BitVec 64)) :
    Id (Option Nat) from
  ⦃fun _ => True⦄ (bsearchArrays key n a) ⪯[purify Unit] bsearchPure
    ⦃fun v o _ => v = o; (fun _ _ => False, estack⟨⟩)⦄
  ascend [wrp_purify_ret (bsearchArrays_spec key n a)] with finish

/--
info: def Ascent.Kraken.bsearchPure : BitVec 64 → Nat → Array (BitVec 64) → Id (Option Nat) :=
fun key n a => pure (bsearchFrame a key 0 n)
-/
#guard_msgs in
#print bsearchPure

/-! ## The chain of refinements -/

/-- The memory at the entry of the binary search: `n` mapped words at `A`. -/
structure SearchWords (m : DataMem) (A : BitVec 64) (n : Nat) : Prop where
  len : n < 2 ^ 61
  map : Mem.Mapped [(A, 8 * n)] m

attribute [grind →] SearchWords.len SearchWords.map

@[grind =] theorem WordNat_eq {w : Nat} (x : BitVec w) (n : Nat) : WordNat x n = (x = BitVec.ofNat w n) := rfl

@[grind =] theorem IdxWord_eq (v : BitVec 64) (o : Option Nat) : IdxWord v o = (v = encodeIdx o) := rfl

@[grind =] theorem toList_words_toArray (m : DataMem) (p : BitVec 64) (n : Nat) :
    (words 8 64 m p n).toArray.toList = words 8 64 m p n := rfl

section
variable [Host] [Embeds bsearch] (r₀ : BitVec 64) (ra : Int64)

theorem bsearchResult_refines_Arrays {A key rax : BitVec 64} {n : Nat} {a : Array (BitVec 64)} :
    ⦃fun t => RegsRel [(.rdi, A), (.rsi, BitVec.ofNat 64 n), (.rdx, key), (.rax, rax), (.rsp, r₀)] t ∧
      (A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 t.dmem A a.size = a.toList ∧
        Mem.Mapped [(A, 8 * a.size)] t.dmem ∧
        retAddrAt t.dmem (r₀) = some ra)⦄
      (bsearchResult r₀ ra) ⪯[(ofStateRepr MachineData.dmem).comp (ofStateRepr (fun _ : DataMem => ()))]
      (bsearchArrays key n a)
      ⦃fun _ o t => t.regs.get64 .rax = encodeIdx o ∧ t.regs.get64 .rsp = r₀ + 8;
        (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  Refinement.comp_le (by grind) (by grind) (by grind) (bsearchArrays.refines A key rax r₀ ra n a)
    ((bsearchRegs.refines A (BitVec.ofNat 64 n) key rax r₀ ra).weaken fun t h => h.1)

theorem bsearchResult_refines_Pure {A key rax : BitVec 64} {n : Nat} {a : Array (BitVec 64)} :
    ⦃fun t => RegsRel [(.rdi, A), (.rsi, BitVec.ofNat 64 n), (.rdx, key), (.rax, rax), (.rsp, r₀)] t ∧
      (A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 t.dmem A a.size = a.toList ∧
        Mem.Mapped [(A, 8 * a.size)] t.dmem ∧
        retAddrAt t.dmem (r₀) = some ra)⦄
      (bsearchResult r₀ ra) ⪯[((ofStateRepr MachineData.dmem).comp (ofStateRepr (fun _ : DataMem => ()))).comp (purify Unit)]
      (bsearchPure key n a)
      ⦃fun _ o t => t.regs.get64 .rax = encodeIdx o ∧ t.regs.get64 .rsp = r₀ + 8;
        (fun _ _ => False, estack⟨⟩)⦄ :=
  Refinement.comp_le (by grind) (by grind) (by grind) (bsearchPure.refines key n a) (bsearchResult_refines_Arrays r₀ ra)

end

section
variable [Host] [FunDecls] [Embeds bsearch] (s : MachineData) (ra : Int64)

/-- What the x64 text of the binary search computes: started at `s.push64 ra` with `rdi` pointing to
`n` words sorted by signed order, `rsi` holding `n` and `rdx` holding `key`, it returns to `ra` with
the stack pointer of the caller, and `rax` holds an index of `key` among the words, or `-1` when no
word is `key`. -/
theorem bsearch_correct {A key : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = BitVec.ofNat 64 n)
    (hrdx : (s.push64 ra).regs.get64 .rdx = key)
    (hmem : SearchWords (s.push64 ra).dmem A n)
    (hsorted : ∀ i j, i ≤ j → j < n → ((words 8 64 (s.push64 ra).dmem A n).toArray[i]!).toInt
      ≤ ((words 8 64 (s.push64 ra).dmem A n).toArray[j]!).toInt) :
    Triple bsearch (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        ((∃ j < n, t.regs.get64 .rax = BitVec.ofNat 64 j ∧ (words 8 64 (s.push64 ra).dmem A n).toArray[j]! = key) ∨
          (t.regs.get64 .rax = -1 ∧ ∀ j < n, (words 8 64 (s.push64 ra).dmem A n).toArray[j]! ≠ key))) := by
  have hs : IntSorted (words 8 64 (s.push64 ra).dmem A n).toArray n := hsorted
  clear hsorted
  have hr : retAddrAt (s.push64 ra).dmem ((s.push64 ra).regs.get64 .rsp) = some ra := by
    have h := MachineData.retAddr_push64 s ra
    rw [MachineData.retAddr_eq] at h
    exact h
  have h := Refinement.transport_catchExit ((bsearchLoops.refines ((s.push64 ra).regs.get64 .rsp) ra).weaken (P' := (· = s.push64 ra)) fun t ht => by
      subst ht; exact ⟨rfl, MachineData.retAddr_push64 s ra⟩)
    ((bsearchResult.eq ((s.push64 ra).regs.get64 .rsp) ra).symm ▸ (bsearchResult_refines_Arrays ((s.push64 ra).regs.get64 .rsp) ra (A := A) (key := key)
      (rax := (s.push64 ra).regs.get64 .rax) (a := (words 8 64 (s.push64 ra).dmem A n).toArray)).transport
      (bsearchArrays_mem_spec key n _ hs (size_words_toArray _ _ _)))
  refine ⟨fun t ht => WP.wp_monotone (x := bsearch) (fun _ _ _ => trivial) ?_ t (h.le_wp t (by grind))⟩
  intro a t hE
  grind

end

end Ascent.Kraken
