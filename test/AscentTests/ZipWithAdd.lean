import Ascent.Corres.Loop
import Std.Tactic.Do

/-!
# Case study: `zip_with_add` abstracted to `Array.zipWith`

The C function

```c
size_t zip_with_add(const int *a, size_t len_a, const int *b, size_t len_b, int *out) {
    size_t n = len_a < len_b ? len_a : len_b;
    for (size_t i = 0; i < n; i++) out[i] = a[i] + b[i];
    return n;
}
```

abstracted from its memory-level denotation `zipL1` to the pure `Array.zipWith (· + ·)`, through
the AutoCorres-style levels L1 → L2 → L3 → L4: reflect the locals (L1 → L2), reflect the heap onto
arrays (L2 → L3), realize the loop as a `zipWith` (L3 → L4), assemble the entry.
-/

open Std.Internal.Do Lean.Order Ascent

set_option mvcgen.warning false

namespace Zip

/-! ## Programs

All definitions: the memory model and primitives, the L1 denotation, the three loops, the closed
form, the spec, and the concretization couplings. -/

abbrev Addr := Nat

abbrev I    := Int32                          -- C `int`

structure Heap where
  data  : Addr → I
  valid : Addr → Bool                         -- heap type description: where c_guard succeeds

abbrev Ident := String

inductive Value                               -- minimal untyped value domain (cf. CLight's CVal)
  | int  (v : I)
  | ptr  (a : Addr)
  | size (n : USize)

abbrev Locals := Ident → Option Value

structure State where
  locals : Locals
  heap   : Heap

abbrev M := StateT State UB                    -- state (locals + heap) + UB; no ExceptT

/-- Memory load (well-defined only after `c_guard`). -/
def load (p : Addr) : M I := fun s => pure (s.heap.data p, s)

/-- Memory store. -/
def store (p : Addr) (v : I) : M Unit :=
  fun s => pure (⟨⟩, { s with heap.data := fun a => if a = p then v else s.heap.data a })

/-- The parser's `c_guard`: UB unless `p` is a valid pointer. -/
def cguard (p : Addr) : M Unit := fun s => if s.heap.valid p then pure (⟨⟩, s) else UB.fail

/-- Read a `size_t` local; UB if missing or wrong type. -/
def getSize (x : Ident) : M USize := fun s => match s.locals x with | some (.size n) => pure (n, s) | _ => UB.fail

/-- Read a pointer local; UB if missing or wrong type. -/
def getPtr (x : Ident) : M Addr := fun s => match s.locals x with | some (.ptr a) => pure (a, s) | _ => UB.fail

/-- Write a `size_t` local. -/
def setSize (x : Ident) (n : USize) : M Unit :=
  fun s => pure (⟨⟩, { s with locals := fun y => if y = x then some (.size n) else s.locals y })

/-- The loop guard: `i < n`, reading both from the locals. -/
def guardL1 : State → Bool := fun s =>
  match s.locals "i", s.locals "n" with
  | some (.size i), some (.size n) => decide (i < n)
  | _, _ => false

/-- The loop body: `out[i] = a[i] + b[i]; i++`, with a `c_guard` before each access. -/
def stepL1 : M Unit := do
  let i   ← getSize "i"
  let a   ← getPtr "a"
  let b   ← getPtr "b"
  let out ← getPtr "out"
  cguard (a + i.toNat);   let x ← load (a + i.toNat)
  cguard (b + i.toNat);   let y ← load (b + i.toNat)
  cguard (out + i.toNat); store (out + i.toNat) (x + y)     -- Int32 wrapping +, no overflow guard
  setSize "i" (i + 1)

/-- L1 denotation of `zip_with_add`. -/
def zipL1 : M USize := do
  let la ← getSize "len_a"
  let lb ← getSize "len_b"
  setSize "n" (min la lb)              -- size_t n = len_a < len_b ? len_a : len_b;
  setSize "i" 0
  whileLoop guardL1 stepL1                            -- for (i = 0; i < n; i++)
  getSize "n"                                            -- return n;

/-- Single-cell heap update. -/
def Heap.upd (h : Heap) (p : Addr) (v : I) : Heap :=
  { h with data := fun a => if a = p then v else h.data a }

/-- The abstract loop carries `(counter, heap)`; the guard is `i < n` for the fixed bound `n`. -/
def guardL2 (n : USize) : USize × Heap → Bool := fun p => decide (p.1 < n)

/-- The abstract body: guard the three accesses, write `out[i] = a[i] + b[i]`, increment the
counter. The heap-only counterpart of `stepL1`. -/
def stepL2 (a b out : Addr) : StateT (USize × Heap) UB Unit := fun p =>
  let i := p.1; let h := p.2
  if h.valid (a + i.toNat) && h.valid (b + i.toNat) && h.valid (out + i.toNat) then
    pure ((), (i + 1, h.upd (out + i.toNat) (h.data (a + i.toNat) + h.data (b + i.toNat))))
  else UB.fail

/-- The loop invariant: the abstract counter and heap match the concrete `i` local and heap, and the
pointer/bound locals hold their fixed values. -/
def invL2 (a b out : Addr) (n : USize) : USize × Heap → State → Prop := fun p s =>
  s.heap = p.2 ∧ s.locals "i" = some (.size p.1) ∧ s.locals "n" = some (.size n) ∧
  s.locals "a" = some (.ptr a) ∧ s.locals "b" = some (.ptr b) ∧ s.locals "out" = some (.ptr out)

/-- Every access in the loop range is to a valid address. -/
def AllValid (a b out : Addr) (n : Nat) (h : Heap) : Prop :=
  ∀ j, j < n → h.valid (a + j) = true ∧ h.valid (b + j) = true ∧ h.valid (out + j) = true

/-- The output region is disjoint from both input regions over the loop range. -/
def NoAlias (a b out : Addr) (n : Nat) : Prop :=
  ∀ i j, i < n → j < n → out + i ≠ a + j ∧ out + i ≠ b + j

/-- A flat memory region `[p, p + n)`, read out as an array. -/
def slice (p : Addr) (n : Nat) (h : Heap) : Array I := Array.ofFn (n := n) fun j => h.data (p + j.val)

/-- The function-entry coupling: the locals hold the C arguments. -/
def entryP (a b out : Addr) (la lb : USize) : State → Prop := fun s =>
  s.locals "len_a" = some (.size la) ∧ s.locals "len_b" = some (.size lb) ∧
  s.locals "a" = some (.ptr a) ∧ s.locals "b" = some (.ptr b) ∧ s.locals "out" = some (.ptr out)

/-- The out-param loop's guard: `i < n`. -/
def guardL3 (n : USize) : USize × Array I → Bool := fun p => decide (p.1 < n)

/-- The out-param loop's body: guard the three accesses against the array bounds, write
`out[i] = a[i] + b[i]`, increment `i`. -/
def stepL3 (a b : Array I) : StateT (USize × Array I) UB Unit := fun p =>
  if p.1.toNat < a.size ∧ p.1.toNat < b.size ∧ p.1.toNat < p.2.size then
    pure ((), (p.1 + 1, p.2.setIfInBounds p.1.toNat (a.getD p.1.toNat 0 + b.getD p.1.toNat 0)))
  else UB.fail

/-- Closed form: `out` with its first `k` cells overwritten by `a[j] + b[j]`. -/
def zippedL3 (a b : Array I) (k : Nat) (out : Array I) : Array I :=
  Array.ofFn (n := out.size) fun j => if j.val < k then a.getD j.val 0 + b.getD j.val 0 else out[j]

/-- The heap→array loop coupling: the abstract `(i, out_arr)` reflects the concrete `(i, heap)` by
slicing the three regions; validity is invariant, so it rides along. -/
def invL3 (a b out : Addr) (n : USize) (a_arr b_arr : Array I) :
    USize × Array I → USize × Heap → Prop := fun pa ph =>
  pa.1 = ph.1 ∧ pa.2 = slice out n.toNat ph.2 ∧
  slice a n.toNat ph.2 = a_arr ∧ slice b n.toNat ph.2 = b_arr ∧ AllValid a b out n.toNat ph.2

/-- The out-param spec: the out array becomes `Array.zipWith (· + ·)` of the inputs, the return is the
length. -/
def zipL4 (a b : Array I) (n : USize) : StateT (Array I) UB USize := do
  set <| Array.zipWith (· + ·) a b
  pure n

/-- The fully pure spec: no state monad, the output array is the return value alongside the length. -/
def zipL5 (a b : Array I) (n : USize) : Id (USize × Array I) :=
  pure (n, Array.zipWith (· + ·) a b)

/-! ## Proofs

The `@[spec]` triples, the per-level correspondences (`corres_L1L2` … `corres_L3L4`), the realization,
and the end-to-end `corres_zip`. -/

/-- `omega`, after exposing `Addr` as `Nat` (this toolchain's `omega` does not unfold the abbrev). -/
local macro "aomega" : tactic => `(tactic| (unfold Addr at *; omega))

@[spec] theorem getSize_spec (x : Ident) (post : USize → State → Prop) :
    ⦃(fun s => ∃ v, s.locals x = some (.size v)) ⊓ (fun s => ∀ v, s.locals x = some (.size v) → post v s)⦄
      getSize x ⦃post⦄ := by
  refine Triple.intro ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and] at hs
  obtain ⟨⟨v, hloc⟩, hp⟩ := hs
  simpa [StateT.wp_apply_eq, StateT.run, getSize, hloc] using hp v hloc

@[spec] theorem getPtr_spec (x : Ident) (post : Addr → State → Prop) :
    ⦃(fun s => ∃ a, s.locals x = some (.ptr a)) ⊓ (fun s => ∀ a, s.locals x = some (.ptr a) → post a s)⦄
      getPtr x ⦃post⦄ := by
  refine Triple.intro ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and] at hs
  obtain ⟨⟨a, hloc⟩, hp⟩ := hs
  simpa [StateT.wp_apply_eq, StateT.run, getPtr, hloc] using hp a hloc

@[spec] theorem load_spec (p : Addr) (post : I → State → Prop) :
    ⦃fun s => post (s.heap.data p) s⦄ load p ⦃post⦄ := by
  refine Triple.intro ?_
  intro s hp
  simpa [StateT.wp_apply_eq, StateT.run, load] using hp

@[spec] theorem store_spec (p : Addr) (v : I) (post : Unit → State → Prop) :
    ⦃fun s => post ⟨⟩ { s with heap.data := fun a => if a = p then v else s.heap.data a }⦄
      store p v ⦃post⦄ := by
  refine Triple.intro ?_
  intro s hp
  simpa [StateT.wp_apply_eq, StateT.run, store] using hp

@[spec] theorem cguard_spec (p : Addr) (post : Unit → State → Prop) :
    ⦃fun s => s.heap.valid p = true ∧ post ⟨⟩ s⦄ cguard p ⦃post⦄ := by
  refine Triple.intro ?_
  intro s ⟨hv, hp⟩
  simpa [StateT.wp_apply_eq, StateT.run, cguard, hv] using hp

@[spec] theorem setSize_spec (x : Ident) (n : USize) (post : Unit → State → Prop) :
    ⦃fun s => post ⟨⟩ { s with locals := fun y => if y = x then some (.size n) else s.locals y }⦄
      setSize x n ⦃post⦄ := by
  refine Triple.intro ?_
  intro s hp
  simpa [StateT.wp_apply_eq, StateT.run, setSize] using hp

/-- The abstract body's `wp`, as a function of the state (so it rewrites under the `∃` in the
relational precondition). -/
theorem wp_stepL2 (a b out : Addr) (Q : Unit → USize × Heap → Prop) (E : EPost.Nil)
    (p : USize × Heap) :
    wp (stepL2 a b out) Q E p =
      if p.2.valid (a + p.1.toNat) && p.2.valid (b + p.1.toNat) && p.2.valid (out + p.1.toNat) then
        Q () (p.1 + 1, p.2.upd (out + p.1.toNat) (p.2.data (a + p.1.toNat) + p.2.data (b + p.1.toNat)))
      else (⊥ : Prop) := by
  simp only [stepL2, StateT.wp_apply_eq, StateT.run, wp_ite, UB.wp_pure_eq, UB.wp_fail_eq]

/-- The loop body corresponds: each concrete local read extracts the coupled value, the heap
operations act on the coupled heap, and the counter update evolves the coupling. -/
theorem corres_stepL2 (a b out : Addr) (n : USize) :
    Corres (relRef (invL2 a b out n)) ⊤ (αVeq (id : Unit → Unit)) (stepL2 a b out) stepL1 := by
  intro Q E cs hpre
  simp only [top_meet] at hpre
  obtain ⟨⟨i, h⟩, ⟨hh, hi, hn, ha, hb, hout⟩, habs⟩ := hpre
  subst hh
  rw [wp_stepL2] at habs
  simp only [relRef_γQ, id, invL2, stepL1, wp_bind_StateT]
  simp only [StateT.wp_apply_eq, StateT.run, getSize, getPtr, cguard, load, store, setSize,
    hi, ha, hb, hout, UB.wp_pure_eq, wp_ite, UB.wp_fail_eq]
  simp only [Heap.upd] at habs
  by_cases hv1 : cs.heap.valid (a + i.toNat) = true <;>
    by_cases hv2 : cs.heap.valid (b + i.toNat) = true <;>
    by_cases hv3 : cs.heap.valid (out + i.toNat) = true <;>
    simp only [hv1, hv2, hv3, Bool.and_true, Bool.and_false,
      if_true, if_false, bot_prop_eq, Bool.false_eq_true] at habs ⊢
  exact ⟨(i + 1, _), ⟨rfl, by simp, by simpa using hn, by simp, by simp, by simp⟩, habs⟩

theorem corres_L1L2 (a b out : Addr) (n : USize) :
    Corres (relRef (invL2 a b out n)) ⊤ (αVeq (id : Unit → Unit))
      (whileLoop (guardL2 n) (stepL2 a b out)) (whileLoop guardL1 stepL1) := by
  apply corres_whileLoop (μ := fun p => n.toNat - p.1.toNat)
  · -- guards agree under the coupling
    rintro ⟨i, h⟩ s ⟨hh, hi, hn, ha, hb, hout⟩
    simp [guardL2, guardL1, hi, hn]
  · exact corres_stepL2 a b out n
  · -- the body decreases the variant on success
    rintro E ⟨i, h⟩ hcond hsucc
    simp only [stepL2, StateT.wp_apply_eq, StateT.run, wp_ite, UB.wp_pure_eq, UB.wp_fail_eq,
      bot_prop_eq] at hsucc ⊢
    have hlt : i.toNat < n.toNat := USize.lt_iff_toNat_lt.mp (by simpa [guardL2] using hcond)
    split at hsucc
    · next hv =>
      rw [if_pos hv]
      have hbound : i.toNat + 1 < 2 ^ System.Platform.numBits := by
        have := USize.toNat_lt_two_pow_numBits n; omega
      have heq : (i + 1).toNat = i.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt hbound
      omega
    · exact hsucc.elim

/-- `getSize "n"` (the `return n`) reads the coupled bound, abstracting to `pure n`. -/
theorem corres_getSizeN (a b out : Addr) (n : USize) :
    Corres (relRef (invL2 a b out n)) ⊤ (αVeq (id : USize → USize))
      (pure n : StateT (USize × Heap) UB USize) (getSize "n") := by
  intro Q E cs hpre
  simp only [top_meet] at hpre
  obtain ⟨⟨i, h⟩, hJ, habs⟩ := hpre
  simp only [StateT.wp_apply_eq, StateT.run_pure, UB.wp_pure_eq] at habs
  obtain ⟨hh, hi, hn, ha, hb, hout⟩ := hJ
  simp only [relRef_γQ, id, getSize, StateT.wp_apply_eq, StateT.run, hn, UB.wp_pure_eq]
  exact ⟨(i, h), ⟨hh, hi, hn, ha, hb, hout⟩, habs⟩

/-- The loop together with the trailing `return n`, composed with `corres_bind`. -/
theorem corres_L1L2_tail (a b out : Addr) (n : USize) :
    Corres (relRef (invL2 a b out n)) ⊤ (αVeq (id : USize → USize))
      (whileLoop (guardL2 n) (stepL2 a b out) >>= fun _ => pure n)
      (whileLoop guardL1 stepL1 >>= fun _ => getSize "n") :=
  corres_bind_top id id (corres_L1L2 a b out n) (fun _ => corres_getSizeN a b out n)

/-- Two heaps are equal when their components are. -/
theorem Heap.ext {h₁ h₂ : Heap} (hd : h₁.data = h₂.data) (hv : h₁.valid = h₂.valid) : h₁ = h₂ := by
  cases h₁; cases h₂; cases hd; cases hv; rfl

@[simp] theorem Heap.upd_data (h : Heap) (p : Addr) (v : I) (q : Addr) :
    (h.upd p v).data q = if q = p then v else h.data q := rfl

@[simp] theorem Heap.upd_valid (h : Heap) (p : Addr) (v : I) : (h.upd p v).valid = h.valid := rfl

theorem wp_stepL3 (a b : Array I) (Q : Unit → USize × Array I → Prop) (E : EPost.Nil)
    (p : USize × Array I) :
    wp (stepL3 a b) Q E p =
      if p.1.toNat < a.size ∧ p.1.toNat < b.size ∧ p.1.toNat < p.2.size then
        Q () (p.1 + 1, p.2.setIfInBounds p.1.toNat (a.getD p.1.toNat 0 + b.getD p.1.toNat 0))
      else (⊥ : Prop) := by
  simp only [stepL3, StateT.wp_apply_eq, StateT.run, wp_ite, UB.wp_pure_eq, UB.wp_fail_eq]

@[simp] theorem zippedL3_size (a b : Array I) (k : Nat) (out : Array I) :
    (zippedL3 a b k out).size = out.size := by simp [zippedL3]

@[simp] theorem zippedL3_zero (a b : Array I) (out : Array I) : zippedL3 a b 0 out = out := by
  apply Array.ext
  · simp [zippedL3]
  · intro i hi₁ hi₂; simp [zippedL3]

/-- One step of the loop extends the zipped prefix by a single cell. -/
theorem zippedL3_body (a b : Array I) (k : Nat) (out : Array I) :
    (zippedL3 a b k out).setIfInBounds k (a.getD k 0 + b.getD k 0) = zippedL3 a b (k + 1) out := by
  apply Array.ext
  · simp [zippedL3]
  · intro i hi₁ hi₂
    rw [zippedL3_size] at hi₂
    rw [Array.getElem_setIfInBounds (by rw [zippedL3_size]; exact hi₂)]
    simp only [zippedL3, Array.getElem_ofFn]
    by_cases hik : k = i
    · subst hik; rw [if_pos rfl, if_pos (by omega)]
    · rw [if_neg hik]
      by_cases hlt : i < k
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

/-- The full closed form is the `zipWith`, when the arrays line up at length `n`. -/
theorem zippedL3_full (a b : Array I) (n : Nat) (out : Array I)
    (ha : a.size = n) (hb : b.size = n) (hout : out.size = n) :
    zippedL3 a b n out = Array.zipWith (· + ·) a b := by
  apply Array.ext
  · simp [zippedL3, ha, hb, hout]
  · intro i hi₁ hi₂
    have hi : i < n := by simpa [zippedL3, hout] using hi₁
    have hia : i < a.size := by omega
    have hib : i < b.size := by omega
    simp only [zippedL3, Array.getElem_ofFn, Array.getElem_zipWith]
    rw [if_pos (by omega)]; simp [Array.getD, hia, hib]

/-- The out-param counter-loop, started at `i` on `zippedL3 …ᵢ`, drives any postcondition of the final
`zippedL3 …ₙ`. By induction on the remaining count. -/
theorem wp_realizeL3 (a b : Array I) (n : USize) (R : Array I → Prop) (E : EPost.Nil)
    (out₀ : Array I) (ha : n.toNat ≤ a.size) (hb : n.toNat ≤ b.size) (hout : n.toNat ≤ out₀.size)
    (hR : R (zippedL3 a b n.toNat out₀)) :
    ∀ m : Nat, ∀ i : USize, n.toNat - i.toNat ≤ m → i.toNat ≤ n.toNat →
      wp (whileLoop (guardL3 n) (stepL3 a b)) (fun _ p => R p.2) E (i, zippedL3 a b i.toNat out₀) := by
  intro m
  induction m with
  | zero =>
    intro i hm hle
    have hi : i.toNat = n.toNat := by omega
    have hcondF : ¬ (guardL3 n (i, zippedL3 a b i.toNat out₀) = true) := by
      simp only [guardL3, decide_eq_true_eq, USize.lt_iff_toNat_lt]; omega
    rw [wp_whileLoop, if_neg hcondF, hi]; exact hR
  | succ m ih =>
    intro i hm hle
    by_cases hlt : i.toNat < n.toNat
    · have hsucc : (i + 1).toNat = i.toNat + 1 := by
        have hbound : i.toNat + 1 < 2 ^ System.Platform.numBits := by
          have := USize.toNat_lt_two_pow_numBits n; omega
        rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt hbound
      have hcond : guardL3 n (i, zippedL3 a b i.toNat out₀) = true := by
        simp only [guardL3, decide_eq_true_eq, USize.lt_iff_toNat_lt]; exact hlt
      have hcheck : i.toNat < a.size ∧ i.toNat < b.size ∧
          i.toNat < (zippedL3 a b i.toNat out₀).size := by simp only [zippedL3_size]; omega
      rw [wp_whileLoop, if_pos hcond, wp_stepL3, if_pos hcheck,
        zippedL3_body a b i.toNat out₀, ← hsucc]
      exact ih (i + 1) (by omega) (by omega)
    · have hi : i.toNat = n.toNat := by omega
      have hcondF : ¬ (guardL3 n (i, zippedL3 a b i.toNat out₀) = true) := by
        simp only [guardL3, decide_eq_true_eq, USize.lt_iff_toNat_lt]; omega
      rw [wp_whileLoop, if_neg hcondF, hi]; exact hR

@[simp] theorem slice_size (p : Addr) (n : Nat) (h : Heap) : (slice p n h).size = n := by simp [slice]

theorem usize_toNat_min (la lb : USize) : (min la lb).toNat = min la.toNat lb.toNat := by
  simp [Min.min, USize.le_iff_toNat_le, apply_ite USize.toNat]

/-- `zipWith` of the full input slices equals `zipWith` of the `min`-truncated slices: it only
depends on the common prefix. -/
theorem zipWith_slice_min (a b : Addr) (la lb : USize) (h : Heap) :
    Array.zipWith (· + ·) (slice a la.toNat h) (slice b lb.toNat h)
      = Array.zipWith (· + ·) (slice a (min la lb).toNat h) (slice b (min la lb).toNat h) := by
  have hm := usize_toNat_min la lb
  apply Array.ext
  · simp only [Array.size_zipWith, slice_size]; omega
  · intro j hj1 hj2
    simp only [Array.size_zipWith, slice_size] at hj1
    have hja : j < la.toNat := by omega
    have hjb : j < lb.toNat := by omega
    have hjn : j < (min la lb).toNat := by omega
    simp only [Array.getElem_zipWith, slice, Array.getElem_ofFn]

theorem slice_getD (p : Addr) (n : Nat) (h : Heap) (i : Nat) (hi : i < n) :
    (slice p n h).getD i 0 = h.data (p + i) := by
  simp [Array.getD, slice]; omega

theorem slice_upd_ne (p : Addr) (n : Nat) (h : Heap) (q : Addr) (v : I)
    (hne : ∀ j, j < n → p + j ≠ q) : slice p n (h.upd q v) = slice p n h := by
  apply Array.ext
  · simp
  · intro j hj₁ hj₂
    simp only [slice, Array.getElem_ofFn, Heap.upd_data]
    rw [if_neg (hne j (by simpa using hj₂))]

theorem slice_upd_eq (out : Addr) (n : Nat) (h : Heap) (i : Nat) (v : I) :
    slice out n (h.upd (out + i) v) = (slice out n h).setIfInBounds i v := by
  apply Array.ext
  · simp
  · intro j hj₁ hj₂
    rw [Array.getElem_setIfInBounds (show j < (slice out n h).size by simpa using hj₂)]
    simp only [slice, Array.getElem_ofFn, Heap.upd_data]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (by aomega), if_neg hij]

/-- The body step corresponds: the heap load/store reflect to array get/set. `NoAlias` keeps the input
slices fixed under the output write. -/
theorem corres_stepL3 (a b out : Addr) (n : USize) (a_arr b_arr : Array I)
    (hd : NoAlias a b out n.toNat) :
    Corres (relRef (invL3 a b out n a_arr b_arr)) ⊤ (αVeq (id : Unit → Unit))
      (stepL3 a_arr b_arr) (stepL2 a b out) := by
  intro Q E ch hpre
  simp only [top_meet] at hpre
  obtain ⟨⟨i, oa⟩, ⟨hc, ho, hsa, hsb, hav⟩, habs⟩ := hpre
  obtain ⟨ic, heap⟩ := ch
  simp only at hc ho hsa hsb hav
  subst hc; subst ho
  rw [wp_stepL3] at habs
  have ha_sz : a_arr.size = n.toNat := by rw [← hsa, slice_size]
  have hb_sz : b_arr.size = n.toNat := by rw [← hsb, slice_size]
  rw [wp_stepL2]
  simp only [relRef_γQ, id]
  by_cases hlt : i.toNat < n.toNat
  · rw [if_pos (by rw [ha_sz, hb_sz, slice_size]; exact ⟨hlt, hlt, hlt⟩)] at habs
    have hv := hav i.toNat hlt
    rw [if_pos (by rw [hv.1, hv.2.1, hv.2.2]; rfl)]
    have hva : a_arr.getD i.toNat 0 = heap.data (a + i.toNat) := by
      rw [← hsa]; exact slice_getD a n.toNat heap i.toNat hlt
    have hvb : b_arr.getD i.toNat 0 = heap.data (b + i.toNat) := by
      rw [← hsb]; exact slice_getD b n.toNat heap i.toNat hlt
    refine ⟨(i + 1, (slice out n.toNat heap).setIfInBounds i.toNat
        (a_arr.getD i.toNat 0 + b_arr.getD i.toNat 0)), ⟨rfl, ?_, ?_, ?_, ?_⟩, habs⟩
    · rw [hva, hvb, slice_upd_eq]
    · rw [slice_upd_ne a n.toNat heap (out + i.toNat) _ (fun j hj => by
        have := (hd i.toNat j hlt hj).1; aomega), hsa]
    · rw [slice_upd_ne b n.toNat heap (out + i.toNat) _ (fun j hj => by
        have := (hd i.toNat j hlt hj).2; aomega), hsb]
    · exact hav
  · rw [if_neg (by rw [ha_sz]; intro hcon; exact hlt hcon.1), bot_prop_eq] at habs
    exact habs.elim

theorem corres_L2L3 (a b out : Addr) (n : USize) (a_arr b_arr : Array I)
    (hd : NoAlias a b out n.toNat) :
    Corres (relRef (invL3 a b out n a_arr b_arr)) ⊤ (αVeq (id : Unit → Unit))
      (whileLoop (guardL3 n) (stepL3 a_arr b_arr)) (whileLoop (guardL2 n) (stepL2 a b out)) := by
  apply corres_whileLoop (μ := fun p => n.toNat - p.1.toNat)
  · rintro ⟨i, oa⟩ ⟨ic, heap⟩ ⟨hc, _, _, _, _⟩
    simp only at hc; subst hc
    simp [guardL3, guardL2]
  · exact corres_stepL3 a b out n a_arr b_arr hd
  · rintro E ⟨i, oa⟩ hcond hsucc
    simp only [wp_stepL3, bot_prop_eq] at hsucc ⊢
    have hlt : i.toNat < n.toNat := USize.lt_iff_toNat_lt.mp (by simpa [guardL3] using hcond)
    split at hsucc
    · next hg =>
      rw [if_pos hg]
      have hbound : i.toNat + 1 < 2 ^ System.Platform.numBits := by
        have := USize.toNat_lt_two_pow_numBits n; omega
      have heq : (i + 1).toNat = i.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt hbound
      omega
    · exact hsucc.elim

/-- The loop together with `return n`. -/
theorem corres_L2L3_tail (a b out : Addr) (n : USize) (a_arr b_arr : Array I)
    (hd : NoAlias a b out n.toNat) :
    Corres (relRef (invL3 a b out n a_arr b_arr)) ⊤ (αVeq (id : USize → USize))
      (whileLoop (guardL3 n) (stepL3 a_arr b_arr) >>= fun _ => pure n)
      (whileLoop (guardL2 n) (stepL2 a b out) >>= fun _ => pure n) :=
  corres_bind_top id id (corres_L2L3 a b out n a_arr b_arr hd)
    (fun _ => corres_pure ⊤ id rfl)

/-- The locals lift (`corres_L1L2_tail`, `State ⇝ USize × Heap`) and the heap→array lift
(`corres_L2L3_tail`, `USize × Heap ⇝ USize × Array`) chained by `corres_comp`. Relates the concrete
loop+`return` to the out-param array loop over `USize × Array`, the counter still carried. -/
theorem corres_L1L3 (a b out : Addr) (n : USize) (a_arr b_arr : Array I)
    (hd : NoAlias a b out n.toNat) :
    Corres ((relRef (invL2 a b out n)).comp (relRef (invL3 a b out n a_arr b_arr))) ⊤
      (αVeq (id ∘ id : USize → USize))
      (whileLoop (guardL3 n) (stepL3 a_arr b_arr) >>= fun _ => pure n)
      (whileLoop guardL1 stepL1 >>= fun _ => getSize "n") :=
  corres_comp (corres_L1L2_tail a b out n) (corres_L2L3_tail a b out n a_arr b_arr hd)

/-- Under the loop-entry couplings (`i = 0`, the bound and pointers, the input slices, validity and
non-aliasing), the concrete loop+`return n` abstracts to `zipL4`. The counter is started at `0` from
`i = 0` and projected away; `wp_realizeL3` computes the `zipWith`. -/
theorem corres_L3L4 (a b out : Addr) (n : USize) (a_arr b_arr : Array I)
    (ha : a_arr.size = n.toNat) (hb : b_arr.size = n.toNat) (hd : NoAlias a b out n.toNat) :
    Corres (Concretization.ofStateRepr (fun s : State => slice out n.toNat s.heap))
      (fun s => (s.locals "i" = some (.size 0) ∧ s.locals "n" = some (.size n) ∧
                s.locals "a" = some (.ptr a) ∧ s.locals "b" = some (.ptr b) ∧
                s.locals "out" = some (.ptr out)) ∧
                slice a n.toNat s.heap = a_arr ∧ slice b n.toNat s.heap = b_arr ∧
                AllValid a b out n.toNat s.heap)
      (αVeq (id : USize → USize))
      (zipL4 a_arr b_arr n)
      (whileLoop guardL1 stepL1 >>= fun _ => getSize "n") := by
  intro Q E s hs
  simp only [Concretization.ofStateRepr_γP, meet_apply, meet_prop_eq_and, zipL4, StateT.wp_apply_eq,
    StateT.run] at hs
  obtain ⟨⟨hloc, hsa, hsb, hav⟩, hQspec⟩ := hs
  simp only [Concretization.ofStateRepr_γQ, id]
  have hwp : wp (whileLoop (guardL3 n) (stepL3 a_arr b_arr) >>= fun _ => pure n)
      (fun v p => Q v p.2) E (0, slice out n.toNat s.heap) := by
    rw [wp_bind_StateT]
    have hsp := wp_realizeL3 a_arr b_arr n (fun arr => Q n arr) E (slice out n.toNat s.heap)
      (by omega) (by omega) (by simp [slice_size])
      (by rw [zippedL3_full a_arr b_arr n.toNat (slice out n.toNat s.heap) ha hb
          (slice_size out n.toNat s.heap)]; exact hQspec) n.toNat 0 (by simp) (by simp)
    simp only [StateT.wp_apply_eq, StateT.run_pure, UB.wp_pure_eq]
    simpa using hsp
  have hcl := corres_L1L3 a b out n a_arr b_arr hd (fun v p => Q v p.2) E s (by
    simp only [top_meet, Concretization.comp, Function.comp, relRef_γP]
    exact ⟨(0, s.heap), ⟨rfl, hloc⟩, (0, slice out n.toNat s.heap), ⟨rfl, rfl, hsa, hsb, hav⟩, hwp⟩)
  refine WP.wp_consequence (whileLoop guardL1 stepL1 >>= fun _ => getSize "n") _ _ E ?_ s hcl
  intro cv s' hpost'
  simp only [Concretization.γQ_αVeq, Concretization.comp, Function.comp, relRef_γP, id] at hpost'
  obtain ⟨⟨ic, heap⟩, hlc, ⟨counter, oa⟩, hac, hQ⟩ := hpost'
  rw [hlc.1, ← hac.2.1]
  exact hQ

/-- Reading a coupled `size_t` local extracts its value; the heap-determined abstract state is
untouched. -/
theorem corres_getSizeVal_st {X : Type} (f : Heap → X) (P : State → Prop) (x : Ident) (v : USize)
    (hP : ∀ s, P s → s.locals x = some (.size v)) :
    Corres (Concretization.ofStateRepr (fun s => f s.heap)) P (αVeq (id : USize → USize))
      (pure v : StateT X UB USize) (getSize x) := by
  intro Q E s hs
  simp only [Concretization.ofStateRepr_γP, meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_γQ,
    StateT.wp_apply_eq, StateT.run, getSize, id] at hs ⊢
  rw [hP s hs.1]; exact hs.2

/-- Writing a `size_t` local is invisible to the heap-determined abstract state. -/
theorem corres_setSize_st {X : Type} (f : Heap → X) (P : State → Prop) (x : Ident) (v : USize) :
    Corres (Concretization.ofStateRepr (fun s => f s.heap)) P (αVeq (id : Unit → Unit))
      (pure () : StateT X UB Unit) (setSize x v) := by
  intro Q E s hs
  simp only [Concretization.ofStateRepr_γP, meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_γQ,
    StateT.wp_apply_eq, StateT.run, setSize, UB.wp_pure_eq, id] at hs ⊢
  exact hs.2

/-- **End to end: `zipL1` is `Array.zipWith`.** Under the function-entry coupling, validity, and
non-aliasing, the denotation `zipL1` abstracts to the pure array program `zipL4`: the output
region becomes `Array.zipWith (· + ·)` of the input regions. The entry `getSize`/`setSize` are threaded
through the out-array concretization; `corres_L3L4` discharges the loop and `return n`. -/
theorem corres_zip (a b out : Addr) (la lb : USize) (a_arr b_arr : Array I)
    (ha : a_arr.size = (min la lb).toNat)
    (hb : b_arr.size = (min la lb).toNat)
    (hd : NoAlias a b out (min la lb).toNat) :
    Corres (Concretization.ofStateRepr (fun s : State => slice out (min la lb).toNat s.heap))
      (fun s => entryP a b out la lb s ∧ slice a (min la lb).toNat s.heap = a_arr ∧
                slice b (min la lb).toNat s.heap = b_arr ∧
                AllValid a b out (min la lb).toNat s.heap)
      (αVeq (id : USize → USize)) (zipL4 a_arr b_arr (min la lb)) zipL1 := by
  have key : Corres (Concretization.ofStateRepr (fun s : State => slice out (min la lb).toNat s.heap))
      (fun s => entryP a b out la lb s ∧ slice a (min la lb).toNat s.heap = a_arr ∧
                slice b (min la lb).toNat s.heap = b_arr ∧
                AllValid a b out (min la lb).toNat s.heap)
      (αVeq (id : USize → USize))
      (pure la >>= fun _ => pure lb >>= fun _ => pure () >>= fun _ => pure () >>= fun _ =>
        zipL4 a_arr b_arr (min la lb)) zipL1 := by
    unfold zipL1
    refine corres_bind (fun s => entryP a b out la lb s ∧
        slice a (min la lb).toNat s.heap = a_arr ∧
        slice b (min la lb).toNat s.heap = b_arr ∧
        AllValid a b out (min la lb).toNat s.heap)
      (fun cv1 s => (entryP a b out la lb s ∧
        slice a (min la lb).toNat s.heap = a_arr ∧
        slice b (min la lb).toNat s.heap = b_arr ∧
        AllValid a b out (min la lb).toNat s.heap) ∧ cv1 = la) id id
      (corres_getSizeVal_st (fun h => slice out (min la lb).toNat h) _ "len_a" la (fun s hs => hs.1.1)) ?_ (fun cv1 => ?_)
    · intro E s hs
      simp only [StateT.wp_apply_eq, StateT.run, getSize, hs.1.1, UB.wp_pure_eq]
      exact ⟨hs, trivial⟩
    refine corres_bind _ (fun cv2 s => (entryP a b out la lb s ∧
        slice a (min la lb).toNat s.heap = a_arr ∧
        slice b (min la lb).toNat s.heap = b_arr ∧
        AllValid a b out (min la lb).toNat s.heap) ∧ cv1 = la ∧ cv2 = lb) id id
      (corres_getSizeVal_st (fun h => slice out (min la lb).toNat h) _ "len_b" lb (fun s hs => hs.1.1.2.1)) ?_ (fun cv2 => ?_)
    · intro E s hs
      simp only [StateT.wp_apply_eq, StateT.run, getSize, hs.1.1.2.1, UB.wp_pure_eq]
      exact ⟨hs.1, hs.2, trivial⟩
    refine corres_bind _ (fun _ s => (s.locals "n" = some (.size (min la lb)) ∧
        s.locals "a" = some (.ptr a) ∧ s.locals "b" = some (.ptr b) ∧ s.locals "out" = some (.ptr out)) ∧
        slice a (min la lb).toNat s.heap = a_arr ∧
        slice b (min la lb).toNat s.heap = b_arr ∧
        AllValid a b out (min la lb).toNat s.heap) id id
      (corres_setSize_st (fun h => slice out (min la lb).toNat h) _ "n" _) ?_ (fun _ => ?_)
    · intro E s hs
      obtain ⟨⟨hentry, hsa, hsb, hav⟩, hcv1, hcv2⟩ := hs
      simp only [StateT.wp_apply_eq, StateT.run, setSize, UB.wp_pure_eq, hcv1, hcv2]
      exact ⟨⟨by simp, by simp [hentry.2.2.1], by simp [hentry.2.2.2.1], by simp [hentry.2.2.2.2]⟩,
        hsa, hsb, hav⟩
    refine corres_bind _ (fun _ s => (s.locals "i" = some (.size 0) ∧
        s.locals "n" = some (.size (min la lb)) ∧
        s.locals "a" = some (.ptr a) ∧ s.locals "b" = some (.ptr b) ∧ s.locals "out" = some (.ptr out)) ∧
        slice a (min la lb).toNat s.heap = a_arr ∧
        slice b (min la lb).toNat s.heap = b_arr ∧
        AllValid a b out (min la lb).toNat s.heap) id id
      (corres_setSize_st (fun h => slice out (min la lb).toNat h) _ "i" _) ?_ (fun _ => ?_)
    · intro E s hs
      obtain ⟨⟨hn, hpa, hpb, hpout⟩, hsa, hsb, hav⟩ := hs
      simp only [StateT.wp_apply_eq, StateT.run, setSize, UB.wp_pure_eq]
      exact ⟨⟨by simp, by simp [hn], by simp [hpa], by simp [hpb], by simp [hpout]⟩, hsa, hsb, hav⟩
    exact corres_L3L4 a b out (min la lb) a_arr b_arr ha hb hd
  simpa only [pure_bind] using key

/-- `zipL4`'s `wp`: the write-once spec returns `n` and leaves `Array.zipWith (· + ·)` in the state,
independently of the initial state. -/
theorem wp_zipL4 (a_arr b_arr : Array I) (n : USize) (Q : USize → Array I → Prop) (E : EPost.Nil)
    (s : Array I) : wp (zipL4 a_arr b_arr n) Q E s = Q n (Array.zipWith (· + ·) a_arr b_arr) := by
  rw [zipL4, wp_bind_StateT]
  simp [StateT.wp_apply_eq, UB.wp_pure_eq]

/-- **Dropping the state monad.** Under no precondition, `zipL4` (a state computation over the output
buffer) is abstracted by the pure `zipL5`, which returns the output array as a value. The terminal
`corres_purify` reads the final state into the result. -/
theorem corres_purifyL4 (a_arr b_arr : Array I) (n : USize) :
    Corres (purify (Array I)) ⊤ purifyαV (zipL5 a_arr b_arr n) (zipL4 a_arr b_arr n) := by
  apply corres_purify (zipL4 a_arr b_arr n) n (Array.zipWith (· + ·) a_arr b_arr)
  intro Q E
  apply le_of_forall_le
  intro s
  rw [wp_zipL4]

/-- The composite (`purify` over `ofStateRepr`) postcondition coupling reads the final out-region into
the second component of the abstract pair: a postcondition on the pure result `(cv, arr)` becomes one
on the concrete return `cv` and the out-region `slice out m s'.heap`. -/
theorem zip5_γQ (out : Addr) (m : USize) (Q : USize × Array I → Prop) :
    ((Concretization.ofStateRepr (fun s : State => slice out m.toNat s.heap)).comp
        (purify (Array I))).γQ
      (fun av cv s' => av = (cv, slice out m.toNat s'.heap)) Q
    = fun cv s' => Q (cv, slice out m.toNat s'.heap) := by
  funext cv s'
  simp only [Concretization.γQ, Concretization.comp, Function.comp, Concretization.ofStateRepr_γP, purify,
    iSup_apply, meet_apply, iSup_prop_eq_exists, meet_prop_eq_and]
  apply propext
  constructor
  · rintro ⟨i, rfl, h⟩; exact h
  · intro h; exact ⟨(cv, slice out m.toNat s'.heap), rfl, h⟩

/-- **End to end, in `Id`: `zipL1` is `Array.zipWith` as a returned value.** Composing
`corres_purifyL4` over `corres_zip`, the C denotation `zipL1` is abstracted by the pure `zipL5`,
whose return value carries the output array. The state monad is gone entirely. -/
theorem corres_zip5 (a b out : Addr) (la lb : USize) (a_arr b_arr : Array I)
    (ha : a_arr.size = (min la lb).toNat)
    (hb : b_arr.size = (min la lb).toNat)
    (hd : NoAlias a b out (min la lb).toNat) :
    Corres ((Concretization.ofStateRepr (fun s : State => slice out (min la lb).toNat s.heap)).comp
        (purify (Array I)))
      (fun s => entryP a b out la lb s ∧ slice a (min la lb).toNat s.heap = a_arr ∧
                slice b (min la lb).toNat s.heap = b_arr ∧
                AllValid a b out (min la lb).toNat s.heap)
      (fun av cv s' => av = (cv, slice out (min la lb).toNat s'.heap))
      (zipL5 a_arr b_arr (min la lb)) zipL1 := by
  intro Q E
  have hRHS : (Concretization.ofStateRepr (fun s : State => slice out (min la lb).toNat s.heap)).γQ
        (αVeq id) ((purify (Array I)).γQ purifyαV Q)
      = fun cv s' => Q (cv, slice out (min la lb).toNat s'.heap) := by
    simp only [purify_γQ, Concretization.γQ_αVeq, Concretization.ofStateRepr_γP, id_eq]
  rw [zip5_γQ out (min la lb) Q]
  have hb' := corres_purifyL4 a_arr b_arr (min la lb) Q E
  have hc' := corres_zip a b out la lb a_arr b_arr ha hb hd
    ((purify (Array I)).γQ purifyαV Q) ((purify (Array I)).γE E)
  rw [hRHS] at hc'
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      ((Concretization.ofStateRepr (fun s : State => slice out (min la lb).toNat s.heap)).γP_mono
        (PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl) hb')))) hc'

/-- `zip_with_add` is symmetric in its inputs: the pointwise sum does not depend on argument order. A
property of the pure spec `zipL5`. -/
theorem zipWith_comm (a b : Array I) : Array.zipWith (· + ·) a b = Array.zipWith (· + ·) b a := by
  apply Array.ext
  · simp [Nat.min_comm]
  · intro i h1 h2; simp only [Array.getElem_zipWith]; exact Int32.add_comm _ _

/-- The function-entry precondition of `zip_with_add`: the C arguments are in the locals, the input
regions hold `a_arr`/`b_arr`, and every access in `[0, min la lb)` is valid. -/
def zipPre (a b out : Addr) (la lb : USize) (a_arr b_arr : Array I) : State → Prop := fun s =>
  entryP a b out la lb s ∧ slice a la.toNat s.heap = a_arr ∧ slice b lb.toNat s.heap = b_arr ∧
  AllValid a b out (min la lb).toNat s.heap

/-- **Transport from the pure spec, as a Hoare triple.** Any property `φ` of `zipL5`'s result
`(min la lb, Array.zipWith (· + ·) a_arr b_arr)` transports to a triple on `zipL1`: from the entry
precondition, the return value `cv` and the output region `slice out _ s'.heap` satisfy `φ`. Proving
`φ` against the pure `zipL5` discharges it for the heap-manipulating denotation, with no reasoning
about the loop, the heap, or aliasing. -/
theorem zipL1_spec (a b out : Addr) (la lb : USize) (a_arr b_arr : Array I)
    (hd : NoAlias a b out (min la lb).toNat) (φ : USize × Array I → Prop)
    (hφ : φ (min la lb, Array.zipWith (· + ·) a_arr b_arr)) :
    ⦃ zipPre a b out la lb a_arr b_arr ⦄
    zipL1
    ⦃ fun cv s' => φ (cv, slice out (min la lb).toNat s'.heap) ⦄ := by
  refine Triple.intro ?_
  intro s hs
  obtain ⟨hentry, hsa, hsb, hav⟩ := hs
  have key := corres_zip5 a b out la lb (slice a (min la lb).toNat s.heap)
    (slice b (min la lb).toNat s.heap) (by simp) (by simp) hd φ ⊥ s
  rw [zip5_γQ out (min la lb) φ] at key
  refine key ?_
  simp only [meet_apply, meet_prop_eq_and, Concretization.comp, Function.comp,
    Concretization.ofStateRepr_γP, purify]
  refine ⟨⟨hentry, trivial, trivial, hav⟩, ?_⟩
  show φ (min la lb, Array.zipWith (· + ·) (slice a (min la lb).toNat s.heap)
    (slice b (min la lb).toNat s.heap))
  rw [← zipWith_slice_min a b la lb s.heap, hsa, hsb]
  exact hφ

/-- **Functional correctness.** Each cell of the output region holds the sum of the corresponding
input cells. Proving it on `zipL5` is one `Array.getElem_zipWith`; `zipL1_spec` carries it to the C
denotation, where proving it directly would need the loop invariant. -/
theorem zipL1_correct (a b out : Addr) (la lb : USize) (a_arr b_arr : Array I)
    (hd : NoAlias a b out (min la lb).toNat) :
    ⦃ zipPre a b out la lb a_arr b_arr ⦄
    zipL1
    ⦃ fun _ s' => ∀ i, i < (slice out (min la lb).toNat s'.heap).size →
        (slice out (min la lb).toNat s'.heap)[i]! = a_arr[i]! + b_arr[i]! ⦄ :=
  zipL1_spec a b out la lb a_arr b_arr hd
    (fun p => ∀ i, i < p.2.size → p.2[i]! = a_arr[i]! + b_arr[i]!)
    (by
      intro i hi
      have hia : i < a_arr.size := Nat.lt_of_lt_of_le (Array.size_zipWith ▸ hi) (Nat.min_le_left _ _)
      have hib : i < b_arr.size := Nat.lt_of_lt_of_le (Array.size_zipWith ▸ hi) (Nat.min_le_right _ _)
      rw [getElem!_pos (Array.zipWith (· + ·) a_arr b_arr) i hi, getElem!_pos a_arr i hia,
        getElem!_pos b_arr i hib, Array.getElem_zipWith])

/-- **Symmetry.** The output region holds the pointwise sum in the swapped argument order (hence,
with `zipL1_correct`, in either order). Sourced through the pure `zipL5`. -/
theorem zipL1_commuted (a b out : Addr) (la lb : USize) (a_arr b_arr : Array I)
    (hd : NoAlias a b out (min la lb).toNat) :
    ⦃ zipPre a b out la lb a_arr b_arr ⦄
    zipL1
    ⦃ fun _ s' => slice out (min la lb).toNat s'.heap = Array.zipWith (· + ·) b_arr a_arr ⦄ :=
  zipL1_spec a b out la lb a_arr b_arr hd
    (fun p => p.2 = Array.zipWith (· + ·) b_arr a_arr) (zipWith_comm a_arr b_arr)

/-- **Concatenation distributivity.** However the input regions split at an aligned boundary
(`a1.size = b1.size`), the output region is the concatenation of the two sub-zips. The pure fact is
`Array.zipWith_append`; `zipL1_spec` carries it across the loop and heap to `zipL1`. -/
theorem zipL1_distrib (a b out : Addr) (la lb : USize) (a_arr b_arr : Array I)
    (hd : NoAlias a b out (min la lb).toNat) :
    ⦃ zipPre a b out la lb a_arr b_arr ⦄
    zipL1
    ⦃ fun _ s' => ∀ (a1 a2 b1 b2 : Array I), a_arr = a1 ++ a2 → b_arr = b1 ++ b2 → a1.size = b1.size →
        slice out (min la lb).toNat s'.heap
          = Array.zipWith (· + ·) a1 b1 ++ Array.zipWith (· + ·) a2 b2 ⦄ :=
  zipL1_spec a b out la lb a_arr b_arr hd
    (fun p => ∀ (a1 a2 b1 b2 : Array I), a_arr = a1 ++ a2 → b_arr = b1 ++ b2 → a1.size = b1.size →
        p.2 = Array.zipWith (· + ·) a1 b1 ++ Array.zipWith (· + ·) a2 b2)
    (by rintro a1 a2 b1 b2 rfl rfl hsz; exact Array.zipWith_append hsz)

/-- **The return value is the output length.** `zip_with_add` returns `n`, and `n` is exactly the
length of the output region (`= min la lb`). -/
theorem zipL1_returns_size (a b out : Addr) (la lb : USize) (a_arr b_arr : Array I)
    (ha : a_arr.size = la.toNat) (hb : b_arr.size = lb.toNat)
    (hd : NoAlias a b out (min la lb).toNat) :
    ⦃ zipPre a b out la lb a_arr b_arr ⦄
    zipL1
    ⦃ fun cv s' => cv.toNat = (slice out (min la lb).toNat s'.heap).size ⦄ :=
  zipL1_spec a b out la lb a_arr b_arr hd
    (fun p => p.1.toNat = p.2.size)
    (by rw [Array.size_zipWith, ha, hb]; exact usize_toNat_min la lb)

end Zip
