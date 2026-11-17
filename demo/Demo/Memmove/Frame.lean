import Demo.Memmove.Regs
import Demo.Frame

/-!
# `memmove` with its frame split off

`memmoveFrame₀` is `memmoveRegs₀` over the split state `FState`, synthesized by `distill`, for the
frame `Fr rsp 0 0` of the return slot alone. Every access goes to `dmem` and assumes that it misses
the frame. `memmoveFrame` takes `rsp` for `sp`.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Kraken

distill_def memmoveFrame₀ (rdi rsi rdx rsp sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (memmoveRegs₀ rdi rsi rdx rsp rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 0 0))] memmoveFrame₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [memmoveRegs₀, wrp_forIn_lockstep_bind_unit _ _ (_, _)]
  invariants
  · fun (v : BitVec 64 × BitVec 64) m (v' : BitVec 64 × BitVec 64) => match v, v' with
    | (c, d), (c', d') => c ≐ c' ∧ d ≐ d' ∧ retAddrAt m rsp = some ra
  · fun (v : BitVec 64 × BitVec 64) m (v' : BitVec 64 × BitVec 64) => match v, v' with
    | (c, d), (c', d') => c ≐ c' ∧ d ≐ d' ∧ retAddrAt m rsp = some ra
  with finish

sym_simp_def memmoveFrame (rdi rsi rdx rsp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    memmoveFrame₀ rdi rsi rdx rsp ra
  using pre [] post [memmoveFrame₀, pure_bind, bind_pure_unit]

theorem memmoveFrame.refines (rdi rsi rdx rsp sp : BitVec 64) (ra : Int64) :
    ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
      (memmoveRegs₀ rdi rsi rdx rsp rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 0 0))]
      (memmoveFrame rdi rsi rdx rsp ra)
      ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  memmoveFrame.eq rdi rsi rdx rsp ra ▸ memmoveFrame₀.refines rdi rsi rdx rsp sp ra

#print memmoveFrame

end Distillery.Kraken
