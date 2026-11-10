import Demo.BsearchArr
import Demo.ZipPure

/-!
# The binary search as a pure program

`bsearchF a key lo hi` searches `a[lo, hi)` for `key` the way the machine code does: it looks at the
middle `lo + (hi - lo) / 2`, continues right of it while the element is below `key`, returns the
index when the element is `key`, and continues left of it otherwise. Four equations state the cases:
`bsearchF_of_le` and `bsearchF_found` give the result, and `bsearchF_right` and `bsearchF_left` take
the search on the bounds after one step, `bsearchF a key (mid + 1) hi` or `bsearchF a key lo mid`,
back to `bsearchF a key lo hi`. They are the `grind` theory of the loop proof. `bsearchF_some` and
`bsearchF_none` state the result in terms of membership, and `encodeIdx_bsearchF` states it for the
word of the result: the word of an index of `key`, or `-1` when a sorted `a` holds no `key`.

`bsearchArr_spec` states that the array program returns `bsearchF a key 0 n`. `vcgen` proves it
with the invariant `bsearchF a key lo hi = bsearchF a key 0 n` on the bounds `lo` and `hi`, and
`ascend_def` then synthesizes the pure program `bsearchP`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred ofStateRepr_post_post)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken

def bsearchF (a : Array (BitVec 64)) (key : BitVec 64) (lo hi : Nat) : Option Nat :=
  if hi ≤ lo then none
  else if a[lo + (hi - lo) / 2]!.toInt < key.toInt then bsearchF a key (lo + (hi - lo) / 2 + 1) hi
  else if a[lo + (hi - lo) / 2]!.toInt ≤ key.toInt then some (lo + (hi - lo) / 2)
  else bsearchF a key lo (lo + (hi - lo) / 2)
termination_by hi - lo

section
variable {a : Array (BitVec 64)} {key : BitVec 64} {lo hi : Nat}

theorem bsearchF_of_le (h : hi ≤ lo) : bsearchF a key lo hi = none := by
  rw [bsearchF]; simp [h]

theorem bsearchF_found (h : lo < hi) (hl : ¬a[lo + (hi - lo) / 2]!.toInt < key.toInt)
    (hle : a[lo + (hi - lo) / 2]!.toInt ≤ key.toInt) :
    bsearchF a key lo hi = some (lo + (hi - lo) / 2) := by
  rw [bsearchF]; simp [Nat.not_le.mpr h, hl, hle]

theorem bsearchF_right (h : lo < hi) (hl : a[lo + (hi - lo) / 2]!.toInt < key.toInt) :
    bsearchF a key (lo + (hi - lo) / 2 + 1) hi = bsearchF a key lo hi := by
  conv => rhs; rw [bsearchF]
  simp [Nat.not_le.mpr h, hl]

theorem bsearchF_left (h : lo < hi) (hl : ¬a[lo + (hi - lo) / 2]!.toInt < key.toInt)
    (hle : ¬a[lo + (hi - lo) / 2]!.toInt ≤ key.toInt) :
    bsearchF a key lo (lo + (hi - lo) / 2) = bsearchF a key lo hi := by
  conv => rhs; rw [bsearchF]
  simp [Nat.not_le.mpr h, hl, hle]

theorem bsearchF_some : ∀ {lo hi j : Nat}, bsearchF a key lo hi = some j → lo ≤ j ∧ j < hi ∧ a[j]! = key := by
  intro lo hi j h
  induction lo, hi using bsearchF.induct (a := a) (key := key) with
  | case1 lo hi hle => rw [bsearchF_of_le hle] at h; cases h
  | case2 lo hi hlt hl ih =>
    rw [← bsearchF_right (Nat.lt_of_not_le hlt) hl] at h
    obtain ⟨h1, h2, h3⟩ := ih h
    exact ⟨by omega, h2, h3⟩
  | case3 lo hi hlt hl hle =>
    rw [bsearchF_found (Nat.lt_of_not_le hlt) hl hle] at h
    cases h
    refine ⟨by omega, by omega, ?_⟩
    exact BitVec.eq_of_toInt_eq (by omega)
  | case4 lo hi hlt hl hle ih =>
    rw [← bsearchF_left (Nat.lt_of_not_le hlt) hl hle] at h
    obtain ⟨h1, h2, h3⟩ := ih h
    exact ⟨h1, by omega, h3⟩

theorem bsearchF_none (hs : ∀ i j, i ≤ j → j < a.size → a[i]!.toInt ≤ a[j]!.toInt) :
    ∀ {lo hi : Nat}, hi ≤ a.size → bsearchF a key lo hi = none → ∀ j, lo ≤ j → j < hi → a[j]! ≠ key := by
  intro lo hi hhi h
  induction lo, hi using bsearchF.induct (a := a) (key := key) with
  | case1 lo hi hle => intro j h1 h2; omega
  | case2 lo hi hlt hl ih =>
    rw [← bsearchF_right (Nat.lt_of_not_le hlt) hl] at h
    intro j h1 h2 hj
    by_cases hm : lo + (hi - lo) / 2 + 1 ≤ j
    · exact ih hhi h j hm h2 hj
    · have := hs j (lo + (hi - lo) / 2) (by omega) (by omega)
      rw [hj] at this; omega
  | case3 lo hi hlt hl hle =>
    rw [bsearchF_found (Nat.lt_of_not_le hlt) hl hle] at h; cases h
  | case4 lo hi hlt hl hle ih =>
    rw [← bsearchF_left (Nat.lt_of_not_le hlt) hl hle] at h
    intro j h1 h2 hj
    by_cases hm : j < lo + (hi - lo) / 2
    · exact ih (by omega) h j h1 hm hj
    · have := hs (lo + (hi - lo) / 2) j (by omega) (by omega)
      rw [hj] at this; omega

end

def IntSorted (a : Array (BitVec 64)) (hi : Nat) : Prop :=
  ∀ i j, i ≤ j → j < hi → a[i]!.toInt ≤ a[j]!.toInt

theorem encodeIdx_bsearchF {a : Array (BitVec 64)} {key : BitVec 64} {hi : Nat}
    (hs : IntSorted a hi) (hhi : a.size = hi) :
    (∃ j < hi, encodeIdx (bsearchF a key 0 hi) = BitVec.ofNat 64 j ∧ a[j]! = key) ∨
      (encodeIdx (bsearchF a key 0 hi) = -1 ∧ ∀ j < hi, a[j]! ≠ key) := by
  subst hhi
  cases h : bsearchF a key 0 a.size with
  | none => exact Or.inr ⟨rfl, fun j hj => bsearchF_none hs (Nat.le_refl _) h j (Nat.zero_le j) hj⟩
  | some j =>
    obtain ⟨-, h2, h3⟩ := bsearchF_some h
    exact Or.inl ⟨j, h2, rfl, h3⟩

grind_pattern encodeIdx_bsearchF => encodeIdx (bsearchF a key 0 hi)

attribute [local grind =] bsearchF_of_le bsearchF_found bsearchF_right bsearchF_left in
theorem bsearchArr_spec (key : BitVec 64) (n : Nat) (a : Array (BitVec 64)) :
    ⦃fun _ => True⦄ bsearchArr key n a
      ⦃fun o _ => o = bsearchF a key 0 n; (fun (_ : CfgLabel) (_ : Unit) => False, estack⟨⟩)⦄ := by
  vcgen [bsearchArr]
    invariants
    · WhileInvariant.mk fun (done : Bool) (iko : Nat × Nat × Option Nat) (_ : Unit) =>
        (done = false → iko.1 ≤ iko.2.1 ∧ iko.2.1 ≤ n ∧ bsearchF a key iko.1 iko.2.1 = bsearchF a key 0 n) ∧
        (done = true → iko.2.2 = bsearchF a key 0 n)
    · Variant.ofMeasure fun (iko : Nat × Nat × Option Nat) => iko.2.1 - iko.1
    simp [Variant.evalsBelow_ofMeasure_nat]
    with finish

/-! ## The pure program -/

ascend_def bsearchP (key : BitVec 64) (n : Nat) (a : Array (BitVec 64)) :
    Id (Option Nat) from
  ⦃fun _ => True⦄ (bsearchArr key n a) ⪯[purify Unit] bsearchP
    ⦃fun v o _ => v = o; (fun _ _ => False, estack⟨⟩)⦄
  ascend [wrp_purify_ret (bsearchArr_spec key n a)] with finish

/--
info: def Ascent.Kraken.bsearchP : BitVec 64 → Nat → Array (BitVec 64) → Id (Option Nat) :=
fun key n a => pure (bsearchF a key 0 n)
-/
#guard_msgs in
#print bsearchP

/-! ## The chain of refinements -/

/-- The memory at the entry of the binary search: `n` mapped words at `A`, and the return slot at
`rsp` mapped. -/
structure SearchWords (m : DataMem) (A rsp : BitVec 64) (n : Nat) : Prop where
  len : n < 2 ^ 61
  map : Mem.Mapped [(A, 8 * n)] m
  ret : (Mem.loadInt m rsp 8).isSome = true

attribute [grind →] SearchWords.len SearchWords.map SearchWords.ret

@[grind =] theorem WordNat_eq {w : Nat} (x : BitVec w) (n : Nat) : WordNat x n = (x = BitVec.ofNat w n) := rfl

@[grind =] theorem IdxWord_eq (v : BitVec 64) (o : Option Nat) : IdxWord v o = (v = encodeIdx o) := rfl

@[grind =] theorem toList_words_toArray (m : DataMem) (p : BitVec 64) (n : Nat) :
    (words 8 64 m p n).toArray.toList = words 8 64 m p n := rfl

theorem bsearchR_refines_P {A key rax rsp : BitVec 64} {n : Nat} {a : Array (BitVec 64)}
    (hn : n < 2 ^ 61) :
    ⦃fun t => RegsRel [(.rdi, A), (.rsi, BitVec.ofNat 64 n), (.rdx, key), (.rax, rax), (.rsp, rsp)] t ∧
      (A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 t.dmem A a.size = a.toList ∧
        Mem.Mapped [(A, 8 * a.size)] t.dmem ∧ (Mem.loadInt t.dmem rsp 8).isSome = true)⦄
      bsearchR ⪯[((ofStateRepr MachineData.dmem).comp (ofStateRepr (fun _ : DataMem => ()))).comp (purify Unit)]
      (bsearchP key n a)
      ⦃fun _ o t => t.regs.get64 .rax = encodeIdx o; (fun _ _ => False, estack⟨⟩)⦄ := by
  have hArr : ⦃fun t => RegsRel [(.rdi, A), (.rsi, BitVec.ofNat 64 n), (.rdx, key), (.rax, rax), (.rsp, rsp)] t ∧
      (A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 t.dmem A a.size = a.toList ∧
        Mem.Mapped [(A, 8 * a.size)] t.dmem ∧ (Mem.loadInt t.dmem rsp 8).isSome = true)⦄
      bsearchR ⪯[(ofStateRepr MachineData.dmem).comp (ofStateRepr (fun _ : DataMem => ()))]
      (bsearchArr key n a)
      ⦃fun _ o t => t.regs.get64 .rax = encodeIdx o; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
    Refinement.comp_le (by grind) (by grind) (by grind) (bsearchArr.refines A key rax rsp n a)
      ((bsearchL.refines A (BitVec.ofNat 64 n) key rax rsp).weaken fun t h => h.1)
  exact Refinement.comp_le (by grind) (by grind) (by grind) (bsearchP.refines key n a) hArr

section
variable [Host] [FunDecls] [Embeds bsearch] (s : MachineData) (ra : Int64)

/-- What the x64 text of the binary search computes: started at `s.push64 ra` with `rdi` pointing to
`n` words sorted by signed order, `rsi` holding `n` and `rdx` holding `key`, it returns to `ra` with
the stack pointer of the caller, and `rax` holds an index of `key` among the words, or `-1` when no
word is `key`. -/
theorem bsearch_correct {A key : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = BitVec.ofNat 64 n)
    (hrdx : (s.push64 ra).regs.get64 .rdx = key)
    (hmem : SearchWords (s.push64 ra).dmem A ((s.push64 ra).regs.get64 .rsp) n)
    (hsorted : ∀ i j, i ≤ j → j < n → ((words 8 64 (s.push64 ra).dmem A n).toArray[i]!).toInt
      ≤ ((words 8 64 (s.push64 ra).dmem A n).toArray[j]!).toInt) :
    Triple bsearch (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        ((∃ j < n, t.regs.get64 .rax = BitVec.ofNat 64 j ∧ (words 8 64 (s.push64 ra).dmem A n).toArray[j]! = key) ∨
          (t.regs.get64 .rax = -1 ∧ ∀ j < n, (words 8 64 (s.push64 ra).dmem A n).toArray[j]! ≠ key))) := by
  let t₀ := s.push64 ra
  let arr := (words 8 64 t₀.dmem A n).toArray
  let res := bsearchF arr key 0 n
  have hn := hmem.len
  have hs : IntSorted arr n := hsorted
  clear hsorted
  -- The pure layer, transported to the caught program.
  have hR := (bsearchR_refines_P (A := A) (key := key) (rax := t₀.regs.get64 .rax)
      (rsp := t₀.regs.get64 .rsp) (a := arr) hn).transport
    (Pa := True) (Qa := fun o => o = res) (Ea := estack⟨⟩) ⟨fun _ => by rw [bsearchP, WPMonadExact.wp_pure_eq]⟩
  -- The caught program returns where the structured program throws `exit`.
  have hT : Triple bsearchT (fun t => t = abs t₀) (fun _ t => t.regs.get64 .rax = encodeIdx res)
      (fun l t => l = .exit ∧ t.regs.get64 .rax = encodeIdx res, estack⟨⟩) := by
    refine ⟨fun t ht => ?_⟩
    subst ht
    have h := hR.le_wp (abs t₀) (by
      clear hR
      simp only [meet_apply, meet_prop_eq_and, Concretization.comp_pred, ofStateRepr_pred, purify_pred]
      refine ⟨⟨?_, ?_⟩, trivial⟩ <;> grind)
    clear hR
    rw [← bsearchR.eq, BlockLoop.wp_tryCatch] at h
    refine WP.wp_monotone (x := bsearchT) ?_ ?_ (abs t₀) h
    · intro _ t hq
      simp only [Concretization.post_pi, Concretization.comp_pred, ofStateRepr_pred, purify_pred] at hq
      grind
    · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l t hl
      by_cases he : l = .exit
      · subst he
        simp only [↓reduceIte, WPMonadExact.wp_pure_eq, Concretization.post_pi, Concretization.comp_pred,
          ofStateRepr_pred, purify_pred] at hl
        exact ⟨rfl, by grind⟩
      · simp only [he, ↓reduceIte, BlockLoop.wp_throw] at hl
        grind
  have h := (bsearchT.refines s ra).transport hT
  refine ⟨fun t ht => WP.wp_monotone (x := bsearch) (fun _ _ _ => trivial) ?_ t
    (h.le_wp t (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ⟨ht, ht ▸ rfl⟩))⟩
  intro a t hE
  simp only [ePosts_ret, Concretization.post_pi, ofStateRepr_pred, RetRel_eq, abs_regs] at hE
  obtain ⟨_, ⟨hra, -, hrsp⟩, -, hrax⟩ := hE
  refine ⟨hra, hrsp, ?_⟩
  have hsz := size_words_toArray (s.push64 ra).dmem A n
  simp only [res, arr, t₀] at hrax
  grind

end

end Ascent.Kraken
