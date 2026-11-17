import Demo.Frame
import Demo.Tests.StackFrame.Regs

/-!
# Stack frames split from the data memory

Regression tests for the frame layer on the leaf functions of `Demo.Tests.StackFrame.Regs`. Each `xF₀`
is `xL` over the split state `FState`, synthesized by `distill`, for the frame `Fr rsp 2 0` of two
reserved words and no stack arguments. The precondition marks `rsp` as the stack address `sp` and states
the return address in the return slot. The `#print` of each `xF` records the current result.
-/

open Std.WP Lean.Order Distillery Distillery.Kraken Distillery.Kraken.AInstr
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Kraken.Tests.StackFrame

distill_def pushPopFrame₀ [Host] [Embeds pushPop] (rbx r12 rsp : BitVec 64) (sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (pushPopRegs rbx r12 rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 2 0))] pushPopFrame₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [pushPopRegs]
  with finish

#print pushPopFrame₀

distill_def localsFrame₀ [Host] [Embeds locals] (rdi rsi rsp : BitVec 64) (sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (localsRegs rdi rsi rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 2 0))] localsFrame₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [localsRegs]
  with finish

#print localsFrame₀

distill_def bytesFrame₀ [Host] [Embeds bytes] (rax rsp : BitVec 64) (sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (bytesRegs rax rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 2 0))] bytesFrame₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [bytesRegs]
  with finish

#print bytesFrame₀

distill_def halvesFrame₀ [Host] [Embeds halves] (rax rsp : BitVec 64) (sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (halvesRegs rax rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 2 0))] halvesFrame₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [halvesRegs]
  with finish

#print halvesFrame₀

distill_def redZoneFrame₀ [Host] [Embeds redZone] (rdi rax rsp : BitVec 64) (sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (redZoneRegs rdi rax rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 2 0))] redZoneFrame₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [redZoneRegs]
  with finish

#print redZoneFrame₀

end Distillery.Kraken.Tests.StackFrame

/-! ## Forwarding

Each `xF` is `xF₀` with every load after a store at the same address replaced by the stored
value. -/

namespace Distillery.Kraken.Tests.StackFrame

sym_simp_def pushPopFrame [Host] [Embeds pushPop] (rbx r12 sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    pushPopFrame₀ rbx r12 sp sp ra
  using pre [] post [pushPopFrame₀, loadIn_frame, storeIn_frame, store_load_self, store_load_comm, BitVec.setWidth_eq]

#print pushPopFrame

sym_simp_def localsFrame [Host] [Embeds locals] (rdi rsi sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    localsFrame₀ rdi rsi sp sp ra
  using pre [] post [localsFrame₀, loadIn_frame, storeIn_frame, store_load_self, store_load_comm, BitVec.setWidth_eq]

#print localsFrame

sym_simp_def bytesFrame [Host] [Embeds bytes] (rax sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    bytesFrame₀ rax sp sp ra
  using pre [] post [bytesFrame₀, loadIn_frame, storeIn_frame, store_load_self, store_load_comm, BitVec.setWidth_eq]

#print bytesFrame

sym_simp_def halvesFrame [Host] [Embeds halves] (rax sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    halvesFrame₀ rax sp sp ra
  using pre [] post [halvesFrame₀, loadIn_frame, storeIn_frame, store_load_self, store_load_comm, BitVec.setWidth_eq]

#print halvesFrame

sym_simp_def redZoneFrame [Host] [Embeds redZone] (rdi rax sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    redZoneFrame₀ rdi rax sp sp ra
  using pre [] post [redZoneFrame₀, loadIn_frame, storeIn_frame, store_load_self, store_load_comm, BitVec.setWidth_eq]

#print redZoneFrame

end Distillery.Kraken.Tests.StackFrame
