import Demo.Reverse.Frame
import Demo.ArraysFrame

/-!
# `reverse_` over an array

`reverseArrays₀` is `reverseFrame` over the array of `n` words at `rdi`, synthesized by `ascend`, and
`reverseArrays` is `reverseArrays₀` with the array reads in place. The array is read and written in
place: a load reads the abstract state, and the pointers of the loop become indices into it
(`Index`). The accesses to the frame leave the array unchanged and vanish. The precondition states
the layout `ArrayLayout 8 64 [] rdi n []` of `dmem`, that the array is apart from the frame, and
that the frame is mapped.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def reverseArrays₀ [Host] [Embeds swap] (rdi rsi rax rbx r12 r14 r15 rsp : BitVec 64) (ra : Int64)
    (n : Nat) : BlockM (Array (BitVec 64)) Unit from
  ⦃fun s => rsi ≐ₙ n ∧ ArrayLayout 8 64 [] rdi n [] s.dmem ∧
    Mem.Blocks.Disjoint [(rdi, 8 * n)] (Fr rsp 6 0) ∧ Mem.Mapped (Fr rsp 6 0) s.frame⦄
  (reverseFrame rdi rsi rax rbx r12 r14 r15 rsp ra) ⪯[ofStateRepr fun s : FState => outView 8 64 rdi n s.dmem]
    reverseArrays₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [reverseFrame, wrp_forIn_lockstep_bind_unit _ _ (_, _)]
  invariants
  · fun (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (s : FState) (x : Nat × Nat) =>
      match v, x with
      | (p, q, k, i), (pi, qi) =>
        PureRefinement p pi True (Index 8 rdi) ∧ PureRefinement q qi True (Index 8 rdi) ∧
        k ≐ₙ qi ∧ i ≐ₙ (pi + 1) ∧ pi + qi + 1 = n ∧ pi < qi ∧
        ArrayLayout 8 64 [] rdi n [] s.dmem ∧ Mem.Blocks.Disjoint [(rdi, 8 * n)] (Fr rsp 6 0) ∧
        Mem.Mapped (Fr rsp 6 0) s.frame
  with finish

sym_simp_def reverseArrays (ra : Int64) (n : Nat) : BlockM (Array (BitVec 64)) Unit from reverseArrays₀ ra n
  using pre [] post [reverseArrays₀, BitVec.setWidth_eq, pure_bind, bind_pure_unit, bind_assoc, Nat.zero_add, condState_const]

/--
info: def Ascent.Kraken.reverseArrays : Int64 → Nat → BlockM (Array (BitVec 64)) Unit :=
fun ra n =>
  if n.blt 2 = true then throw ra
  else do
    let mut a := (0, n - 1)
    repeat'
      let x ← get
      let x_1 ← get
      modify fun o => o.set! a.fst x_1[a.snd]!
      modify fun o => o.set! a.snd x[a.fst]!
      if (a.fst + 1).blt (a.snd - 1) = true then 
        a := (a.fst + 1, a.snd - 1)
      else
        throw ra
-/
#guard_msgs in
#print reverseArrays

theorem reverseArrays.refines [Host] [Embeds swap] (rdi rsi rax rbx r12 r14 r15 rsp : BitVec 64) (ra : Int64) (n : Nat) :
    ⦃fun s => rsi ≐ₙ n ∧ ArrayLayout 8 64 [] rdi n [] s.dmem ∧ Mem.Blocks.Disjoint [(rdi, 8 * n)] (Fr rsp 6 0) ∧
      Mem.Mapped (Fr rsp 6 0) s.frame⦄
      (reverseFrame rdi rsi rax rbx r12 r14 r15 rsp ra) ⪯[ofStateRepr fun s : FState => outView 8 64 rdi n s.dmem]
      (reverseArrays ra n) ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  reverseArrays.eq ra n ▸ reverseArrays₀.refines rdi rsi rax rbx r12 r14 r15 rsp ra n

end Ascent.Kraken
