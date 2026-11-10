import Demo.BsearchArr
import Demo.ZipPure

/-!
# The binary search as a pure program

`bsearchF a key lo hi` searches `a[lo, hi)` for `key` the way the machine code does: it looks at the
middle `lo + (hi - lo) / 2`, continues right of it while the element is below `key`, returns the
index when the element is `key`, and continues left of it otherwise. `bsearchArr_spec` states that
the array program returns `bsearchF a key 0 n`, encoded as a word by `encode`; `vcgen` proves it with
the invariant that the remaining search on the bounds gives the same result. `ascend_def` then
synthesizes the pure program `bsearchP`.
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

def encode : Option Nat → BitVec 64
  | none => 18446744073709551615#64
  | some j => BitVec.ofNat 64 j

section
variable {a : Array (BitVec 64)} {key : BitVec 64} {lo hi : Nat}

theorem bsearchF_of_le (h : hi ≤ lo) : bsearchF a key lo hi = none := by
  rw [bsearchF]; simp [h]

theorem bsearchF_right (h : lo < hi) (hl : a[lo + (hi - lo) / 2]!.toInt < key.toInt) :
    bsearchF a key lo hi = bsearchF a key (lo + (hi - lo) / 2 + 1) hi := by
  rw [bsearchF]; simp [Nat.not_le.mpr h, hl]

theorem bsearchF_found (h : lo < hi) (hl : ¬a[lo + (hi - lo) / 2]!.toInt < key.toInt)
    (hle : a[lo + (hi - lo) / 2]!.toInt ≤ key.toInt) :
    bsearchF a key lo hi = some (lo + (hi - lo) / 2) := by
  rw [bsearchF]; simp [Nat.not_le.mpr h, hl, hle]

theorem bsearchF_left (h : lo < hi) (hl : ¬a[lo + (hi - lo) / 2]!.toInt < key.toInt)
    (hle : ¬a[lo + (hi - lo) / 2]!.toInt ≤ key.toInt) :
    bsearchF a key lo hi = bsearchF a key lo (lo + (hi - lo) / 2) := by
  rw [bsearchF]; simp [Nat.not_le.mpr h, hl, hle]


grind_pattern bsearchF_of_le => bsearchF a key lo hi, hi ≤ lo
grind_pattern bsearchF_right => bsearchF a key lo hi, a[lo + (hi - lo) / 2]!.toInt < key.toInt
grind_pattern bsearchF_found => bsearchF a key lo hi, a[lo + (hi - lo) / 2]!.toInt ≤ key.toInt
grind_pattern bsearchF_left => bsearchF a key lo hi, a[lo + (hi - lo) / 2]!

@[grind =] theorem encode_none : encode none = 18446744073709551615#64 := rfl
@[grind =] theorem encode_some (j : Nat) : encode (some j) = BitVec.ofNat 64 j := rfl

theorem bsearchF_some : ∀ {lo hi j : Nat}, bsearchF a key lo hi = some j → lo ≤ j ∧ j < hi ∧ a[j]! = key := by
  intro lo hi j h
  induction lo, hi using bsearchF.induct (a := a) (key := key) with
  | case1 lo hi hle => rw [bsearchF_of_le hle] at h; cases h
  | case2 lo hi hlt hl ih =>
    rw [bsearchF_right (Nat.lt_of_not_le hlt) hl] at h
    obtain ⟨h1, h2, h3⟩ := ih h
    exact ⟨by omega, h2, h3⟩
  | case3 lo hi hlt hl hle =>
    rw [bsearchF_found (Nat.lt_of_not_le hlt) hl hle] at h
    cases h
    refine ⟨by omega, by omega, ?_⟩
    exact BitVec.eq_of_toInt_eq (by omega)
  | case4 lo hi hlt hl hle ih =>
    rw [bsearchF_left (Nat.lt_of_not_le hlt) hl hle] at h
    obtain ⟨h1, h2, h3⟩ := ih h
    exact ⟨h1, by omega, h3⟩

theorem bsearchF_none (hs : ∀ i j, i ≤ j → j < a.size → a[i]!.toInt ≤ a[j]!.toInt) :
    ∀ {lo hi : Nat}, hi ≤ a.size → bsearchF a key lo hi = none → ∀ j, lo ≤ j → j < hi → a[j]! ≠ key := by
  intro lo hi hhi h
  induction lo, hi using bsearchF.induct (a := a) (key := key) with
  | case1 lo hi hle => intro j h1 h2; omega
  | case2 lo hi hlt hl ih =>
    rw [bsearchF_right (Nat.lt_of_not_le hlt) hl] at h
    intro j h1 h2 hj
    by_cases hm : lo + (hi - lo) / 2 + 1 ≤ j
    · exact ih hhi h j hm h2 hj
    · have := hs j (lo + (hi - lo) / 2) (by omega) (by omega)
      rw [hj] at this; omega
  | case3 lo hi hlt hl hle =>
    rw [bsearchF_found (Nat.lt_of_not_le hlt) hl hle] at h; cases h
  | case4 lo hi hlt hl hle ih =>
    rw [bsearchF_left (Nat.lt_of_not_le hlt) hl hle] at h
    intro j h1 h2 hj
    by_cases hm : j < lo + (hi - lo) / 2
    · exact ih (by omega) h j h1 hm hj
    · have := hs (lo + (hi - lo) / 2) j (by omega) (by omega)
      rw [hj] at this; omega

end

theorem bsearchArr_spec (key : BitVec 64) (n : Nat) (a : Array (BitVec 64)) :
    ⦃fun _ => True⦄ bsearchArr key n a
      ⦃fun _ _ => False; (fun (l : CfgLabel) (_ : Unit) => l = .ret (encode (bsearchF a key 0 n)), estack⟨⟩)⦄ := by
  vcgen [bsearchArr]
    invariants
    · WhileInvariant.mk fun (done : Bool) (ik : Nat × Nat) (_ : Unit) =>
        done = false ∧ ik.1 ≤ ik.2 ∧ ik.2 ≤ n ∧ bsearchF a key ik.1 ik.2 = bsearchF a key 0 n
    · Variant.ofMeasure fun (ik : Nat × Nat) => ik.2 - ik.1
    simp [Variant.evalsBelow_ofMeasure_nat]
    with finish

/-! ## The pure program -/

ascend_def bsearchP (key : BitVec 64) (n : Nat) (a : Array (BitVec 64)) : Id (Option Nat) from
  ⦃fun _ => True⦄ (bsearchArr key n a) ⪯[purify Unit] bsearchP
    ⦃fun _ _ _ => False; (fun l _ => l = .ret (encode (Id.run bsearchP)), estack⟨⟩)⦄
  ascend [wrp_purify_throwVal (f := fun r => CfgLabel.ret (encode r)) (bsearchArr_spec key n a)] with finish

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

@[grind =] theorem toList_words_toArray (m : DataMem) (p : BitVec 64) (n : Nat) :
    (words 8 64 m p n).toArray.toList = words 8 64 m p n := rfl

theorem bsearchT_refines_Arr {A key rsp : BitVec 64} {n : Nat} {a : Array (BitVec 64)} :
    ⦃fun t => RegsRel [(.rdi, A), (.rsi, BitVec.ofNat 64 n), (.rdx, key), (.rsp, rsp)] t ∧
      (A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 t.dmem A a.size = a.toList ∧
        Mem.Mapped [(A, 8 * a.size)] t.dmem ∧ (Mem.loadInt t.dmem rsp 8).isSome = true)⦄
      bsearchT ⪯[(ofStateRepr MachineData.dmem).comp (ofStateRepr (fun _ : DataMem => ()))]
      (bsearchArr key n a)
      ⦃fun _ _ _ => True; (fun l l' t => l = .exit ∧
        ∃ j, t.regs.get64 .rax = BitVec.ofNat 64 j ∧ l' = .ret (BitVec.ofNat 64 j), estack⟨⟩)⦄ := by
  exact Refinement.comp_le (by grind) (by grind) (by grind) (bsearchArr.refines A key rsp n a)
    ((bsearchL.refines A (BitVec.ofNat 64 n) key rsp).weaken fun t h => h.1)

theorem bsearchT_refines_P {A key rsp : BitVec 64} {n : Nat} {a : Array (BitVec 64)} :
    ⦃fun t => RegsRel [(.rdi, A), (.rsi, BitVec.ofNat 64 n), (.rdx, key), (.rsp, rsp)] t ∧
      (A ≐ₐ a ∧ a.size = n ∧ n < 2 ^ 61 ∧ words 8 64 t.dmem A a.size = a.toList ∧
        Mem.Mapped [(A, 8 * a.size)] t.dmem ∧ (Mem.loadInt t.dmem rsp 8).isSome = true)⦄
      bsearchT ⪯[((ofStateRepr MachineData.dmem).comp (ofStateRepr (fun _ : DataMem => ()))).comp (purify Unit)]
      (bsearchP key n a)
      ⦃fun _ _ _ => False; (fun l t => l = .exit ∧
        t.regs.get64 .rax = encode (Id.run (bsearchP key n a)), estack⟨⟩)⦄ := by
  exact Refinement.comp_le (by grind) (by grind) (by grind) (bsearchP.refines key n a)
    bsearchT_refines_Arr

section
variable [Host] [FunDecls] [Embeds bsearch] (s : MachineData) (ra : Int64)

theorem bsearch_refines_P {A key : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = BitVec.ofNat 64 n)
    (hrdx : (s.push64 ra).regs.get64 .rdx = key)
    (hmem : SearchWords (s.push64 ra).dmem A ((s.push64 ra).regs.get64 .rsp) n) :
    ⦃(· = s.push64 ra)⦄ bsearch
      ⪯[(ofStateRepr abs).comp
        (((ofStateRepr MachineData.dmem).comp (ofStateRepr (fun _ : DataMem => ()))).comp (purify Unit))]
      (bsearchP key n (words 8 64 (s.push64 ra).dmem A n).toArray)
      ⦃fun _ _ _ => False; fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        t.regs.get64 .rax = encode (Id.run (bsearchP key n (words 8 64 (s.push64 ra).dmem A n).toArray))⦄ := by
  exact Refinement.comp_le (by grind) (by grind) (by grind)
    (bsearchT_refines_P (A := A) (rsp := (s.push64 ra).regs.get64 .rsp))
    (bsearchT.refines s ra)

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
  have h := (bsearch_refines_P s ra hrdi hrsi hrdx hmem).transport
    (Pa := True) (Qa := fun _ => True) (Ea := estack⟨⟩) ⟨fun _ => trivial⟩
  refine ⟨fun t ht => WP.wp_monotone (x := bsearch) (fun _ _ _ => trivial) ?_ t
    (h.le_wp t (by simp only [meet_apply, meet_prop_eq_and, Concretization.comp_pred,
      ofStateRepr_pred, purify_pred]; exact ⟨ht, trivial⟩))⟩
  rintro a t ⟨hra, hrsp, hrax⟩
  refine ⟨hra, hrsp, ?_⟩
  simp only [bsearchP, Id.run_pure] at hrax
  have hsz := size_words_toArray (s.push64 ra).dmem A n
  cases hb : bsearchF (words 8 64 (s.push64 ra).dmem A n).toArray key 0 n with
  | none =>
    rw [hb, encode_none] at hrax
    refine Or.inr ⟨hrax.trans rfl, fun j hj => bsearchF_none (by rw [hsz]; exact hsorted) (by omega) hb j
      (Nat.zero_le j) hj⟩
  | some j =>
    rw [hb, encode_some] at hrax
    obtain ⟨-, h2, h3⟩ := bsearchF_some hb
    exact Or.inl ⟨j, h2, hrax, h3⟩

end

end Ascent.Kraken
