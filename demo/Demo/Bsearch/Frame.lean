import Demo.Bsearch.Regs
import Demo.Frame

/-!
# The binary search with its frame split off

`bsearchFrame₀` is `bsearchRegs₀` over the split state `FState`, synthesized by `ascend`, for the
frame `Fr rsp 0 0` of the return slot alone. Every access goes to `dmem` and assumes that it misses
the frame. `bsearchFrame` takes `rsp` for `sp`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def bsearchFrame₀ (rdi rsi rdx rax rsp sp : BitVec 64) (ra : Int64) : BlockM FState (BitVec 64) from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (bsearchRegs₀ rdi rsi rdx rax rsp rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 0 0))] bsearchFrame₀
  ⦃fun v v' _ => v ≐ v'; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [bsearchRegs₀, wrp_forIn_lockstep_bind _ _ _ (_, _, _)]
  invariants
  · fun (v : BitVec 64 × BitVec 64 × BitVec 64) m (v' : BitVec 64 × BitVec 64 × BitVec 64) => match v, v' with
    | (c, d, r), (c', d', r') => c ≐ c' ∧ d ≐ d' ∧ r ≐ r' ∧ retAddrAt m rsp = some ra
  · fun (v : BitVec 64 × BitVec 64 × BitVec 64) _ (v' : BitVec 64 × BitVec 64 × BitVec 64) => match v, v' with
    | (c, d, r), (c', d', r') => c ≐ c' ∧ d ≐ d' ∧ r ≐ r'
  with finish

sym_simp_def bsearchFrame (rdi rsi rdx rax rsp : BitVec 64) : BlockM FState (BitVec 64) from
    bsearchFrame₀ rdi rsi rdx rax rsp
  using pre [] post [bsearchFrame₀, pure_bind, bind_pure_unit, bind_pure]

theorem bsearchFrame.refines (rdi rsi rdx rax rsp sp : BitVec 64) (ra : Int64) :
    ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
      (bsearchRegs₀ rdi rsi rdx rax rsp rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 0 0))]
      (bsearchFrame rdi rsi rdx rax rsp)
      ⦃fun v v' _ => v ≐ v'; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  bsearchFrame.eq rdi rsi rdx rax rsp ▸ bsearchFrame₀.refines rdi rsi rdx rax rsp sp ra

#print bsearchFrame

end Ascent.Kraken
