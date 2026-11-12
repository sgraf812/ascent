import Demo.Frame
import Demo.Tests.StackFrameL

/-!
# Stack frames split from the data memory

Regression tests for the frame layer on the leaf functions of `Demo.Tests.StackFrameL`. Each `xF₀`
is `xL` over the split state `FState`, synthesized by `ascend`, for the frame `Fr rsp 2 0` of two
reserved words and no stack arguments. The precondition marks `rsp` as the stack address `sp` and states
the return address in the return slot. The `#print` of each `xF` records the current result.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken.Tests.StackFrame

ascend_def pushPopF₀ [Host] [Embeds pushPop] (rbx r12 rsp : BitVec 64) (sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (pushPopL rbx r12 rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 2 0))] pushPopF₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [pushPopL]
  with finish

#print pushPopF₀

ascend_def localsF₀ [Host] [Embeds locals] (rdi rsi rsp : BitVec 64) (sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (localsL rdi rsi rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 2 0))] localsF₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [localsL]
  with finish

#print localsF₀

ascend_def bytesF₀ [Host] [Embeds bytes] (rax rsp : BitVec 64) (sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (bytesL rax rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 2 0))] bytesF₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [bytesL]
  with finish

#print bytesF₀

ascend_def halvesF₀ [Host] [Embeds halves] (rax rsp : BitVec 64) (sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (halvesL rax rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 2 0))] halvesF₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [halvesL]
  with finish

#print halvesF₀

ascend_def redZoneF₀ [Host] [Embeds redZone] (rdi rax rsp : BitVec 64) (sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
  ⦃fun m => rsp ≐ₛ sp ∧ retAddrAt m rsp = some ra⦄
  (redZoneL rdi rax rsp ra) ⪯[ofStateRepr (FState.split (Fr rsp 2 0))] redZoneF₀
  ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [redZoneL]
  with finish

#print redZoneF₀

end Ascent.Kraken.Tests.StackFrame

/-! ## Forwarding

Each `xF` is `xF₀` with every load after a store at the same address replaced by the stored
value. -/

namespace Ascent.Kraken.Tests.StackFrame

sym_simp_def pushPopF [Host] [Embeds pushPop] (rbx r12 sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    pushPopF₀ rbx r12 sp sp ra
  using pre [] post [pushPopF₀, loadIn_frame, storeIn_frame, store_load_self, store_load_comm, BitVec.setWidth_eq]

#print pushPopF

sym_simp_def localsF [Host] [Embeds locals] (rdi rsi sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    localsF₀ rdi rsi sp sp ra
  using pre [] post [localsF₀, loadIn_frame, storeIn_frame, store_load_self, store_load_comm, BitVec.setWidth_eq]

#print localsF

sym_simp_def bytesF [Host] [Embeds bytes] (rax sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    bytesF₀ rax sp sp ra
  using pre [] post [bytesF₀, loadIn_frame, storeIn_frame, store_load_self, store_load_comm, BitVec.setWidth_eq]

#print bytesF

sym_simp_def halvesF [Host] [Embeds halves] (rax sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    halvesF₀ rax sp sp ra
  using pre [] post [halvesF₀, loadIn_frame, storeIn_frame, store_load_self, store_load_comm, BitVec.setWidth_eq]

#print halvesF

sym_simp_def redZoneF [Host] [Embeds redZone] (rdi rax sp : BitVec 64) (ra : Int64) : BlockM FState Unit from
    redZoneF₀ rdi rax sp sp ra
  using pre [] post [redZoneF₀, loadIn_frame, storeIn_frame, store_load_self, store_load_comm, BitVec.setWidth_eq]

#print redZoneF

end Ascent.Kraken.Tests.StackFrame
