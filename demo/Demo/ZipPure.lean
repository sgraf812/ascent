import Demo.ZipL
import Demo.Words

/-!
# What `zipWithAdd` computes, from the lifted program

`wp_zipWithAddL` states the result of `zipWithAddL` as the pure function `List.zipWith (· + ·)` on
the arrays it reads, and `zipWithAdd_correct` carries it back to the x64 text through
`zipWithAddS` and the first layer.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open scoped Program.WP

namespace Ascent.Kraken

/-- The memory at the entry of `zipWithAdd`: arrays `A`, `B` and `O` of `n` mapped words, the output
array apart from the inputs and from the return slot at `rsp`, and the return slot mapped. -/
structure ZipArrays (m : DataMem) (A B O rsp : BitVec 64) (n : Nat) : Prop where
  len : n < 2 ^ 61
  mapA : Mem.Mapped [(A, 8 * n)] m
  mapB : Mem.Mapped [(B, 8 * n)] m
  mapO : Mem.Mapped [(O, 8 * n)] m
  disjA : Mem.Blocks.Disjoint [(O, 8 * n)] [(A, 8 * n)]
  disjB : Mem.Blocks.Disjoint [(O, 8 * n)] [(B, 8 * n)]
  disjR : Mem.Blocks.Disjoint [(rsp, 8)] [(O, 8 * n)]
  ret : (Mem.loadInt m rsp 8).isSome = true

theorem wp_zipWithAddL {m : DataMem} {A B O rsp : BitVec 64} {n : Nat} (h : ZipArrays m A B O rsp n) :
    wp (zipWithAddL A B O (BitVec.ofNat 64 n) rsp) (fun _ _ => False)
      (fun l m' => l = .exit ∧ words m' O n = List.zipWith (· + ·) (words m A n) (words m B n),
        estack⟨⟩) m := by
  have hlen := h.len
  unfold zipWithAddL
  by_cases hn0 : n = 0
  · subst hn0
    rw [cmp_le_self_zero]
    simp only [↓reduceIte, wp_retAt]
    exact ⟨h.ret, trivial, by simp [words]⟩
  rw [cmp_le_self_of_pos (Nat.pos_of_ne_zero hn0) hlen]
  simp only [Bool.false_eq_true, ↓reduceIte, WPMonadExact.wp_bind_eq]
  -- The loop, from iteration `k` with the memory after `k` iterations.
  suffices hloop : ∀ j k, n - k = j → k < n →
      wp (FixLoop.mk.forIn (BitVec.ofNat 64 k) fun _ (__s : BitVec 64) => do
        let x ← load8 (B + __s * 8)
        let y ← load8 (A + __s * 8)
        store8 rsp (O + __s * 8) (y + x)
        if (!CondCode.cmp .nz (BitVec.ofNat 64 n) (__s + 1)) = true then pure (ForInStep.done (__s + 1))
          else pure (ForInStep.yield (__s + 1)))
        (fun _ => wp (retAt rsp) (fun _ _ => False)
          (fun l m' => l = .exit ∧ words m' O n = List.zipWith (· + ·) (words m A n) (words m B n),
            estack⟨⟩))
        (fun l m' => l = .exit ∧ words m' O n = List.zipWith (· + ·) (words m A n) (words m B n),
          estack⟨⟩)
        (stores m A B O k) by
    exact hloop n 0 (Nat.sub_zero n) (Nat.pos_of_ne_zero hn0)
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro k hj hk
    rw [FixLoop.forIn_eq]
    simp only [WPMonadExact.wp_bind_eq, wp_load8, wp_store8]
    have hwA : BitVec.ofInt 64 (Mem.loadInt (stores m A B O k) (cell A k) 8).get!
        = word m A k := word_stores_of_disjoint h.disjA hlen hk (Nat.le_of_lt hk)
    have hwB : BitVec.ofInt 64 (Mem.loadInt (stores m A B O k) (cell B k) 8).get!
        = word m B k := word_stores_of_disjoint h.disjB hlen hk (Nat.le_of_lt hk)
    have hst : Mem.storeInt (stores m A B O k) (cell O k) 8 (word m A k + word m B k).toInt
        = stores m A B O (k + 1) := rfl
    show (Mem.loadInt (stores m A B O k) (cell B k) 8).isSome = true ∧ _
    rw [show B + BitVec.ofNat 64 k * 8 = cell B k from rfl, show A + BitVec.ofNat 64 k * 8 = cell A k from rfl,
      show O + BitVec.ofNat 64 k * 8 = cell O k from rfl, hwA, hwB, hst, cmp_nz_succ hk hlen]
    refine ⟨Mem.Mapped.loadInt_isSome (stores_mapped h.mapB k) (cell_inside hk hlen),
      Mem.Mapped.loadInt_isSome (stores_mapped h.mapA k) (cell_inside hk hlen),
      ⟨Mem.Mapped.loadInt_isSome (stores_mapped h.mapO k) (cell_inside hk hlen),
        Mem.Blocks.Disjoint.of_inside_right_pair h.disjR (cell_inside hk hlen)⟩, ?_⟩
    by_cases hkn : k + 1 = n
    · simp only [hkn, ne_eq, not_true_eq_false, decide_false, Bool.not_false, ↓reduceIte,
        WPMonadExact.wp_pure_eq, wp_retAt]
      have hslot : Mem.loadInt (stores m A B O n) rsp 8 = Mem.loadInt m rsp 8 :=
        loadInt_stores_of_disjoint n fun i hi =>
          Mem.Blocks.Disjoint.of_inside_right_pair h.disjR (cell_inside hi hlen)
      rw [← hkn] at hslot ⊢
      refine ⟨by rw [hslot]; exact h.ret, trivial, ?_⟩
      rw [hkn]
      exact words_stores_out hlen
    · simp only [hkn, ne_eq, not_false_eq_true, decide_true, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, WPMonadExact.wp_pure_eq]
      rw [ofNat_succ]
      exact ih (n - (k + 1)) (by omega) (k + 1) rfl (by omega)

/-! ## The machine code -/

section
variable [Host] [FunDecls] [Embeds zipWithAdd]

/-- What the x64 text computes: started at `s.push64 ra` with `rdi`, `rsi`, `rdx` pointing to the
arrays and `rcx` holding their length `n`, it returns to `ra` with the stack pointer of the caller,
and the output array holds `List.zipWith (· + ·)` of the inputs. -/
theorem zipWithAdd_correct (s : MachineData) (ra : Int64) {A B O : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    Triple zipWithAdd (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
        ∧ words t.dmem O n = List.zipWith (· + ·) (words (s.push64 ra).dmem A n)
            (words (s.push64 ra).dmem B n)) := by
  let t₀ := s.push64 ra
  let rsp := t₀.regs.get64 .rsp
  let Ea : (CfgLabel → DataMem → Prop) × EStack⟨⟩ :=
    (fun l m' => l = .exit ∧ words m' O n = List.zipWith (· + ·) (words t₀.dmem A n) (words t₀.dmem B n),
      estack⟨⟩)
  have hL := wp_zipWithAddL hmem
  have hS := wp_zipWithAddS_of_L (rdi := A) (rsi := B) (rdx := O) (rcx := BitVec.ofNat 64 n)
    (rsp := rsp) Ea (abs t₀) ⟨hrdi, hrsi, hrdx, hrcx, rfl, rfl⟩ hL
  have hA := wp_zipWithAddA_of_S s ra _ _ (abs t₀) hS
  have hT := Refinement.transport (zipWithAddA.refines s ra)
    (Pa := (· = abs t₀)) ⟨fun t ht => by subst ht; exact hA⟩
  refine ⟨fun t ht => ?_⟩
  refine WP.wp_monotone (x := zipWithAdd) ?_ ?_ t (hT.le_wp t ?_)
  · intro _ _ _
    trivial
  · intro a t' h'
    change (Concretization.ofStateRepr abs).post (RetRel s ra) _ a t' at h'
    rw [Concretization.post_pi] at h'
    obtain ⟨l', ⟨hra, -, hrsp⟩, h''⟩ := h'
    simp only [Concretization.ofStateRepr_pred] at h''
    obtain ⟨⟨-, hwords⟩, -⟩ := h''
    exact ⟨hra, hrsp, hwords⟩
  · simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred]
    exact ⟨ht, by rw [ht]⟩

end

end Ascent.Kraken
