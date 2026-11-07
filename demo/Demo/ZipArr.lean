import Demo.ZipL
import Demo.Arrays

/-!
# `zipWithAdd` over arrays

`zipWithAddArr` is `zipWithAddL` over the output array, synthesized by `ascend`. The input arrays
are the parameters `a` and `b`, named by their base addresses `A` and `B`. The relation of the loop
states the layout of the memory: the input arrays hold `a` and `b`, the three arrays are mapped,
the output array is apart from the inputs and from the return slot at `rsp`, and the return slot is
mapped.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

/-- The memory of `zipWithAdd` holds the input arrays `a` and `b` at `A` and `B`, and has room for
the output array at `O`. -/
structure ZipLayout (A B O rsp : BitVec 64) (n : Nat) (a b : Array (BitVec 64)) (m : DataMem) :
    Prop where
  len : n < 2 ^ 61
  sizeA : a.size = n
  sizeB : b.size = n
  wordsA : words m A n = a.toList
  wordsB : words m B n = b.toList
  mapA : Mem.Mapped [(A, 8 * n)] m
  mapB : Mem.Mapped [(B, 8 * n)] m
  mapO : Mem.Mapped [(O, 8 * n)] m
  disjA : Mem.Blocks.Disjoint [(O, 8 * n)] [(A, 8 * n)]
  disjB : Mem.Blocks.Disjoint [(O, 8 * n)] [(B, 8 * n)]
  disjR : Mem.Blocks.Disjoint [(rsp, 8)] [(O, 8 * n)]
  ret : (Mem.loadInt m rsp 8).isSome = true

attribute [grind →] ZipLayout.len ZipLayout.sizeA ZipLayout.sizeB ZipLayout.wordsA
  ZipLayout.wordsB ZipLayout.mapA ZipLayout.mapB ZipLayout.mapO ZipLayout.disjA ZipLayout.disjB
  ZipLayout.disjR ZipLayout.ret

theorem ZipLayout.storeInt_out {A B O rsp : BitVec 64} {n : Nat} {a b : Array (BitVec 64)}
    {m : DataMem} (h : ZipLayout A B O rsp n a b m) {v : BitVec 64} (hv : v.toNat < n) (x : Int) :
    ZipLayout A B O rsp n a b (Mem.storeInt m (O + v * 8#64) 8 x) where
  len := h.len
  sizeA := h.sizeA
  sizeB := h.sizeB
  wordsA := by rw [add_mul_eight, words_storeInt_of_disjoint h.disjA hv h.len]; exact h.wordsA
  wordsB := by rw [add_mul_eight, words_storeInt_of_disjoint h.disjB hv h.len]; exact h.wordsB
  mapA := Mem.Mapped.storeInt h.mapA _ _ _
  mapB := Mem.Mapped.storeInt h.mapB _ _ _
  mapO := Mem.Mapped.storeInt h.mapO _ _ _
  disjA := h.disjA
  disjB := h.disjB
  disjR := h.disjR
  ret := by rw [add_mul_eight, loadInt_storeInt_cell_of_disjoint h.disjR hv h.len]; exact h.ret

grind_pattern ZipLayout.storeInt_out =>
  Mem.storeInt m (O + v * 8#64) 8 x, ZipLayout A B O rsp n a b m

end Ascent.Kraken

namespace Ascent.Kraken

ascend_def zipWithAddArr [Host] [FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)
    (A B O rsp : BitVec 64) (n : Nat) (a b : Array (BitVec 64)) :
    BlockM (Array (BitVec 64)) Unit from
  ⦃fun m => A ≐ₐ a ∧ B ≐ₐ b ∧ ZipLayout A B O rsp n a b m⦄
  (zipWithAddL s ra A B O (BitVec.ofNat 64 n) rsp) ⪯[ofStateRepr (outView O n)] zipWithAddArr
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_forIn_diag_bind_unit
    (I := fun m (v : BitVec 64) => v.toNat < n ∧ ZipLayout A B O rsp n a b m)]
    with finish

end Ascent.Kraken
