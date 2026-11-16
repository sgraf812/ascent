import Demo.Reverse.Arrays

/-!
# What `reverse_` computes, from the array program

`reverseArrays_spec` states the result of the synthesized array program `reverseArrays`: it exits
with the array reversed. `vcgen` proves it with the loop invariant "the cells outside `[i, j]` hold
the reversed values, the cells inside hold the input" and the measure `j - i`. `ascend_def`
synthesizes the pure program `reversePure` from this result through `wrp_purify_throw`.

`Refinement.comp_le` composes the refinements of the layers into `reverse_refines_Pure`, from the
x64 text to `reversePure` on the input array. `reverse_correct` is one `Refinement.transport` of the
composition, with the output array read back as memory words.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred ofStateRepr_post_post)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken

theorem reverseArrays_spec {ra : Int64} {n : Nat} {a : Array (BitVec 64)} (ha : a.size = n) :
    ⦃(· = a)⦄ reverseArrays ra n
      ⦃fun _ _ => False; (fun (l : Int64) (o' : Array (BitVec 64)) => l = ra ∧ o' = a.reverse, estack⟨⟩)⦄ := by
  vcgen [reverseArrays]
    invariants
    · WhileInvariant.mk fun (done : Bool) (ij : Nat × Nat) (o' : Array (BitVec 64)) =>
        done = false ∧ o'.size = n ∧ ij.1 + ij.2 + 1 = n ∧ ij.1 < ij.2 ∧
          (∀ k, k < ij.1 → o'[k]! = a[n - 1 - k]!) ∧ (∀ k, ij.2 < k → k < n → o'[k]! = a[n - 1 - k]!) ∧
          (∀ k, ij.1 ≤ k → k ≤ ij.2 → o'[k]! = a[k]!)
    · Variant.ofMeasure fun (ij : Nat × Nat) => ij.2 - ij.1
    simp [Variant.evalsBelow_ofMeasure_nat]
    with finish

/-! ## The pure program -/

ascend_def reversePure (ra : Int64) (n : Nat) (a : Array (BitVec 64)) (ha : a.size = n) : Id (Array (BitVec 64)) from
  ⦃(· = a)⦄ (reverseArrays ra n) ⪯[purify (Array (BitVec 64))] reversePure
    ⦃fun _ _ _ => False; (fun l o => l = ra ∧ o = Id.run reversePure, estack⟨⟩)⦄
  ascend [wrp_purify_throw (reverseArrays_spec ha)] with finish

/--
info: def Ascent.Kraken.reversePure : Array (BitVec 64) → Id (Array (BitVec 64)) :=
fun a => pure a.reverse
-/
#guard_msgs in
#print reversePure

/-! ## The chain of refinements -/

attribute [grind =] reversePure

/-- The memory at the entry of `reverse_`: an array `A` of `n` mapped words apart from the frame of
six words and the return slot at `rsp`, and the frame mapped. -/
structure ReverseArray (m : DataMem) (A rsp : BitVec 64) (n : Nat) : Prop where
  len : n < 2 ^ 61
  mapA : Mem.Mapped [(A, 8 * n)] m
  apart : Mem.Blocks.Disjoint [(A, 8 * n)] (Fr rsp 6 0)
  frame : Mem.Mapped (Fr rsp 6 0) m

attribute [grind →] ReverseArray.len ReverseArray.apart

@[grind →] theorem ReverseArray.layout {m : DataMem} {A rsp : BitVec 64} {n : Nat} (h : ReverseArray m A rsp n) :
    ArrayLayout 8 64 [] A n (FState.split (Fr rsp 6 0) m).dmem where
  width := by omega
  bits := rfl
  len := h.len
  mapped := Mapped.split h.mapA h.apart
  inputs := trivial

@[grind →] theorem ReverseArray.frame_split {m : DataMem} {A rsp : BitVec 64} {n : Nat} (h : ReverseArray m A rsp n) :
    Mem.Mapped (Fr rsp 6 0) (FState.split (Fr rsp 6 0) m).frame :=
  Mapped.split_frame h.frame

section
variable [Host] [FunDecls] [Embeds swap] (rsp : BitVec 64) (ra : Int64)

theorem reverseRegs_refines_Arrays {rdi rax rbx r12 r14 r15 : BitVec 64} {n : Nat} :
    ⦃fun m => (rsp ≐ₛ rsp ∧ retAddrAt m rsp = some ra) ∧
      (BitVec.ofNat 64 n ≐ₙ n ∧ ArrayLayout 8 64 [] rdi n (FState.split (Fr rsp 6 0) m).dmem ∧
        Mem.Blocks.Disjoint [(rdi, 8 * n)] (Fr rsp 6 0) ∧ Mem.Mapped (Fr rsp 6 0) (FState.split (Fr rsp 6 0) m).frame)⦄
      (reverseRegs rdi (BitVec.ofNat 64 n) rax rbx r12 r14 r15 rsp ra)
      ⪯[(ofStateRepr (FState.split (Fr rsp 6 0))).comp (ofStateRepr fun s : FState => outView 8 64 rdi n s.dmem)]
      (reverseArrays ra n)
      ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  Refinement.comp_le (by grind) (by grind) (by grind) (reverseArrays.refines rdi (BitVec.ofNat 64 n) rax rbx r12 r14 r15 rsp ra n)
    ((reverseFrame.refines rdi (BitVec.ofNat 64 n) rax rbx r12 r14 r15 rsp ra).weaken fun _ h => h.1)

theorem reverseLoops_refines_Arrays {rdi rax rbx rbp r12 r13 r14 r15 : BitVec 64} {n : Nat} :
    ⦃fun t => RegsRel [(.rdi, rdi), (.rsi, BitVec.ofNat 64 n), (.rax, rax), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp),
        (.r12, r12), (.r13, r13), (.r14, r14), (.r15, r15)] t ∧
      ((rsp ≐ₛ rsp ∧ retAddrAt t.dmem rsp = some ra) ∧
        (BitVec.ofNat 64 n ≐ₙ n ∧ ArrayLayout 8 64 [] rdi n (FState.split (Fr rsp 6 0) t.dmem).dmem ∧
          Mem.Blocks.Disjoint [(rdi, 8 * n)] (Fr rsp 6 0) ∧
          Mem.Mapped (Fr rsp 6 0) (FState.split (Fr rsp 6 0) t.dmem).frame))⦄
      (reverseLoops (fun r ra => swapLoops r ra) rsp ra)
      ⪯[(ofStateRepr MachineData.dmem).comp ((ofStateRepr (FState.split (Fr rsp 6 0))).comp
        (ofStateRepr fun s : FState => outView 8 64 rdi n s.dmem))]
      (reverseArrays ra n)
      ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = rsp + 8, estack⟨⟩)⦄ :=
  Refinement.comp_le (by grind) (by grind) (by grind) (reverseRegs_refines_Arrays rsp ra)
    ((reverseRegs.refines rdi (BitVec.ofNat 64 n) rax rbx rbp r12 r13 r14 r15 rsp ra).weaken fun _ h => h.1)

theorem reverseLoops_refines_Pure {rdi rax rbx rbp r12 r13 r14 r15 : BitVec 64} {n : Nat} {a : Array (BitVec 64)}
    (ha : a.size = n) :
    ⦃fun t => (RegsRel [(.rdi, rdi), (.rsi, BitVec.ofNat 64 n), (.rax, rax), (.rsp, rsp), (.rbx, rbx), (.rbp, rbp),
        (.r12, r12), (.r13, r13), (.r14, r14), (.r15, r15)] t ∧
      ((rsp ≐ₛ rsp ∧ retAddrAt t.dmem rsp = some ra) ∧
        (BitVec.ofNat 64 n ≐ₙ n ∧ ArrayLayout 8 64 [] rdi n (FState.split (Fr rsp 6 0) t.dmem).dmem ∧
          Mem.Blocks.Disjoint [(rdi, 8 * n)] (Fr rsp 6 0) ∧
          Mem.Mapped (Fr rsp 6 0) (FState.split (Fr rsp 6 0) t.dmem).frame))) ∧
      outView 8 64 rdi n (FState.split (Fr rsp 6 0) t.dmem).dmem = a⦄
      (reverseLoops (fun r ra => swapLoops r ra) rsp ra)
      ⪯[memToArray 8 64 rsp rdi 6 n]
      (reversePure a)
      ⦃fun _ _ _ => False; (fun l t => l = ra ∧ t.regs.get64 .rsp = rsp + 8 ∧
        outView 8 64 rdi n (FState.split (Fr rsp 6 0) t.dmem).dmem = Id.run (reversePure a), estack⟨⟩)⦄ :=
  Refinement.comp_le (by grind) (by grind) (by grind) (reversePure.refines ra n a ha)
    ((reverseLoops_refines_Arrays rsp ra).weaken fun _ h => h.1)

end

section
variable [Host] [FunDecls] [Embeds swap] [Embeds reverse] (s : MachineData) (ra : Int64)

theorem reverse_refines_Pure (hg : FunDecls.at (label "_swap") = some ⟨swap⟩) {A : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = BitVec.ofNat 64 n)
    (hmem : ReverseArray (s.push64 ra).dmem A ((s.push64 ra).regs.get64 .rsp) n) :
    ⦃(· = s.push64 ra)⦄ reverse
      ⪯[machineToArray 8 64 ((s.push64 ra).regs.get64 .rsp) A 6 n]
      (reversePure (words 8 64 (s.push64 ra).dmem A n).toArray)
      ⦃fun _ _ _ => False; fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        outView 8 64 A n (FState.split (Fr ((s.push64 ra).regs.get64 .rsp) 6 0) t.dmem).dmem
          = Id.run (reversePure (words 8 64 (s.push64 ra).dmem A n).toArray)⦄ := by
  have hr : retAddrAt (s.push64 ra).dmem ((s.push64 ra).regs.get64 .rsp) = some ra := by
    have h := MachineData.retAddr_push64 s ra
    rw [MachineData.retAddr_eq] at h
    exact h
  exact Refinement.comp_le (by grind) (by grind) (by grind)
    (reverseLoops_refines_Pure ((s.push64 ra).regs.get64 .rsp) ra (rdi := A)
      (rax := (s.push64 ra).regs.get64 .rax) (rbx := (s.push64 ra).regs.get64 .rbx)
      (rbp := (s.push64 ra).regs.get64 .rbp) (r12 := (s.push64 ra).regs.get64 .r12)
      (r13 := (s.push64 ra).regs.get64 .r13) (r14 := (s.push64 ra).regs.get64 .r14)
      (r15 := (s.push64 ra).regs.get64 .r15) (size_words_toArray _ _ _))
    ((reverseLoops.refines ⟨swap⟩ hg (fun r ra => swapLoops r ra) (fun r ra => swapLoops.refines r ra)
      ((s.push64 ra).regs.get64 .rsp) ra).weaken fun t ht => by
      subst ht; exact ⟨rfl, MachineData.retAddr_push64 s ra⟩)

omit [Host] [FunDecls] [Embeds swap] [Embeds reverse] in
@[grind →] theorem words_eq_reverse_of_outView {m m' : DataMem} {A : BitVec 64} {n : Nat}
    (h : outView 8 64 A n m' = (words 8 64 m A n).toArray.reverse) :
    words 8 64 m' A n = (words 8 64 m A n).reverse := by
  have := congrArg Array.toList h
  simpa only [outView, List.toList_toArray, Array.toList_reverse] using this

/-- What the x64 text computes: started at `s.push64 ra` with `rdi` pointing to the array and `rsi`
holding its length `n`, it returns to `ra` with the stack pointer of the caller, and the array holds
the reverse of its input. -/
theorem reverse_correct (hg : FunDecls.at (label "_swap") = some ⟨swap⟩) {A : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = BitVec.ofNat 64 n)
    (hmem : ReverseArray (s.push64 ra).dmem A ((s.push64 ra).regs.get64 .rsp) n) :
    Triple reverse (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
        ∧ words 8 64 t.dmem A n = (words 8 64 (s.push64 ra).dmem A n).reverse) := by
  have h := (reverse_refines_Pure s ra hg hrdi hrsi hmem).transport
    (Pa := True) (Qa := fun _ => True) (Ea := estack⟨⟩) ⟨fun _ => trivial⟩
  refine ⟨fun t ht => WP.wp_monotone (x := reverse) (fun _ _ _ => trivial) ?_ t (h.le_wp t (by grind))⟩
  intro a t hE
  have hA := hmem.apart
  have hn := hmem.len
  grind [outView_split]

end

end Ascent.Kraken
