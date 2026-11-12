import Demo.ZipL
import Demo.Frame

/-!
# `zipWithAdd` with its frame split off

`zipWithAddF₀` is `zipWithAddL` over the split state `FState`, synthesized by `ascend`, for the frame
`Fr rsp 0 0` of the return slot alone. Every access goes to `dmem` and assumes that it misses the
frame. The precondition marks `rsp` as the stack address `sp` and states the return address in the
return slot, so the return needs no guard. `zipWithAddF` takes `rsp` for `sp`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def zipWithAddF₀ (rdi rsi rdx rcx rsp sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (zipWithAddL₀ rdi rsi rdx rcx rsp rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 0 0))] zipWithAddF₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [zipWithAddL₀, wrp_forIn_lockstep_bind_unit
    (R := fun (v : BitVec 64) m (v' : BitVec 64) => v ≐ v' ∧ retAddrAt m rsp = some ra)]
  with finish

sym_simp_def zipWithAddF (rdi rsi rdx rcx rsp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    zipWithAddF₀ rdi rsi rdx rcx rsp ra
  using pre [] post [zipWithAddF₀, pure_bind, bind_pure_unit]

theorem zipWithAddF.refines (rdi rsi rdx rcx rsp sp : BitVec 64) (ra : Int64) :
    ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
      (zipWithAddL₀ rdi rsi rdx rcx rsp rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 0 0))]
      (zipWithAddF rdi rsi rdx rcx rsp ra)
      ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  zipWithAddF.eq rdi rsi rdx rcx rsp ra ▸ zipWithAddF₀.refines rdi rsi rdx rcx rsp sp ra

#print zipWithAddF

end Ascent.Kraken
