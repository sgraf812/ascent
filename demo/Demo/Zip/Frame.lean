import Demo.Zip.Regs
import Demo.Frame

/-!
# `zipWithAdd` with its frame split off

`zipWithAddFrame₀` is `zipWithAddRegs` over the split state `FState`, synthesized by `distill`, for the frame
`Fr rsp 0 0` of the return slot alone. Every access goes to `dmem` and assumes that it misses the
frame. The precondition marks `rsp` as the stack address `sp` and states the return address in the
return slot, so the return needs no guard. `zipWithAddFrame` takes `rsp` for `sp`.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Kraken

distill_def zipWithAddFrame₀ (rdi rsi rdx rcx rsp sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (zipWithAddRegs₀ rdi rsi rdx rcx rsp rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 0 0))] zipWithAddFrame₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [zipWithAddRegs₀, wrp_forIn_lockstep_bind_unit (R := _)]
  invariants
  · fun (v : BitVec 64) m (v' : BitVec 64) => v ≐ v' ∧ retAddrAt m rsp = some ra
  with finish

sym_simp_def zipWithAddFrame (rdi rsi rdx rcx rsp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    zipWithAddFrame₀ rdi rsi rdx rcx rsp ra
  using pre [] post [zipWithAddFrame₀, pure_bind, bind_pure_unit]

theorem zipWithAddFrame.refines (rdi rsi rdx rcx rsp sp : BitVec 64) (ra : Int64) :
    ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
      (zipWithAddRegs₀ rdi rsi rdx rcx rsp rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 0 0))]
      (zipWithAddFrame rdi rsi rdx rcx rsp ra)
      ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  zipWithAddFrame.eq rdi rsi rdx rcx rsp ra ▸ zipWithAddFrame₀.refines rdi rsi rdx rcx rsp sp ra

#print zipWithAddFrame

end Distillery.Kraken
