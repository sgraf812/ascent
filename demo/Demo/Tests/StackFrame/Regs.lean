import Demo.Regs
import Demo.Tests.StackFrame.Loops

/-!
# Stack frames with their registers lifted

Regression tests for the register layer on the leaf functions of `Demo.Tests.StackFrame.Loops`. Each
`xL₀` is `xT` over the data memory alone, synthesized by `ascend`, and `xL` instantiates the frame
parameter `r₀` with the entry value of `rsp`. The `#print` of each `xL` records the current result.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken.Tests.StackFrame

ascend_def pushPopRegs₀ [Host] [Embeds pushPop] (rdi rsi rbx r12 rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rbx, rbx), (.r12, r12), (.rsp, rsp)]⦄
  (pushPopLoops r₀ ra) ⪯[ofStateRepr MachineData.dmem] pushPopRegs₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [pushPopLoops]
  with finish

sym_simp_def pushPopRegs [Host] [Embeds pushPop] (rbx r12 rsp : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
    pushPopRegs₀ rbx r12 rsp rsp ra
  using pre [add_ofInt_neg] post [stayAt_self, eq_self_iff_true, true_and, assert_true_bind, assert_true, pure_bind,
    bind_pure, pushPopRegs₀, bind_pure_unit, BitVec.sub_add_cancel, BitVec.ofInt_int64ToInt,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg, BitVec.ofNat_eq_ofNat, BitVec.add_neg_eq_sub]

/--
info: def Ascent.Kraken.Tests.StackFrame.pushPopRegs : BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rbx r12 rsp ra => do
  store 8 (rsp - 8#64) rbx
  store 8 (rsp - 8#64 - 8#64) r12
  let _ ← load 8 (rsp - 8#64 - 8#64)
  let _ ← load 8 (rsp - 8#64)
  StateT.assert fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print pushPopRegs

ascend_def localsRegs₀ [Host] [Embeds locals] (rdi rsi rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rsp, rsp)]⦄
  (localsLoops r₀ ra) ⪯[ofStateRepr MachineData.dmem] localsRegs₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [localsLoops]
  with finish

sym_simp_def localsRegs [Host] [Embeds locals] (rdi rsi rsp : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
    localsRegs₀ rdi rsi rsp rsp ra
  using pre [add_ofInt_neg] post [stayAt_self, eq_self_iff_true, true_and, assert_true_bind, assert_true, pure_bind,
    bind_pure, localsRegs₀, bind_pure_unit, BitVec.sub_add_cancel, BitVec.ofInt_int64ToInt,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg, BitVec.ofNat_eq_ofNat, BitVec.add_neg_eq_sub]

/--
info: def Ascent.Kraken.Tests.StackFrame.localsRegs : BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rdi rsi rsp ra => do
  store 8 (rsp - 16#64 + 8#64) rdi
  store 8 (rsp - 16#64) rsi
  let _ ← load 8 (rsp - 16#64 + 8#64)
  let _ ← load 8 (rsp - 16#64)
  StateT.assert fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print localsRegs

ascend_def bytesRegs₀ [Host] [Embeds bytes] (rax rcx rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rax, rax), (.rcx, rcx), (.rsp, rsp)]⦄
  (bytesLoops r₀ ra) ⪯[ofStateRepr MachineData.dmem] bytesRegs₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [bytesLoops]
  with finish

sym_simp_def bytesRegs [Host] [Embeds bytes] (rax rsp : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
    bytesRegs₀ rax rsp rsp ra
  using pre [add_ofInt_neg] post [stayAt_self, eq_self_iff_true, true_and, assert_true_bind, assert_true, pure_bind,
    bind_pure, bytesRegs₀, bind_pure_unit, BitVec.sub_add_cancel, BitVec.ofInt_int64ToInt,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg, BitVec.ofNat_eq_ofNat, BitVec.add_neg_eq_sub]

/--
info: def Ascent.Kraken.Tests.StackFrame.bytesRegs : BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rax rsp ra => do
  store 1 (rsp - 16#64 + 3#64) rax
  let _ ← load 1 (rsp - 16#64 + 3#64)
  let _ ← load 1 (rsp - 16#64 + 3#64)
  StateT.assert fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print bytesRegs

ascend_def halvesRegs₀ [Host] [Embeds halves] (rax rcx rdx rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rax, rax), (.rcx, rcx), (.rdx, rdx), (.rsp, rsp)]⦄
  (halvesLoops r₀ ra) ⪯[ofStateRepr MachineData.dmem] halvesRegs₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [halvesLoops]
  with finish

sym_simp_def halvesRegs [Host] [Embeds halves] (rax rsp : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
    halvesRegs₀ rax rsp rsp ra
  using pre [add_ofInt_neg] post [stayAt_self, eq_self_iff_true, true_and, assert_true_bind, assert_true, pure_bind,
    bind_pure, halvesRegs₀, bind_pure_unit, BitVec.sub_add_cancel, BitVec.ofInt_int64ToInt,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg, BitVec.ofNat_eq_ofNat, BitVec.add_neg_eq_sub]

/--
info: def Ascent.Kraken.Tests.StackFrame.halvesRegs : BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rax rsp ra => do
  store 2 (rsp - 8#64 - 2#64) rax
  let _ ← load 2 (rsp - 8#64 - 2#64)
  store 2 (rsp - 8#64 + 5#64) rax
  let _ ← load 2 (rsp - 8#64 + 5#64)
  StateT.assert fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print halvesRegs

ascend_def redZoneRegs₀ [Host] [Embeds redZone] (rdi rax rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rax, rax), (.rsp, rsp)]⦄
  (redZoneLoops r₀ ra) ⪯[ofStateRepr MachineData.dmem] redZoneRegs₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [redZoneLoops]
  with finish

sym_simp_def redZoneRegs [Host] [Embeds redZone] (rdi rax rsp : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
    redZoneRegs₀ rdi rax rsp rsp ra
  using pre [add_ofInt_neg] post [stayAt_self, eq_self_iff_true, true_and, assert_true_bind, assert_true, pure_bind,
    bind_pure, redZoneRegs₀, bind_pure_unit, BitVec.sub_add_cancel, BitVec.ofInt_int64ToInt,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg, BitVec.ofNat_eq_ofNat, BitVec.add_neg_eq_sub]

/--
info: def Ascent.Kraken.Tests.StackFrame.redZoneRegs : BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rdi rax rsp ra => do
  store 8 (rsp - 8#64) rdi
  store 1 (rsp - 11#64) rax
  let _ ← load 8 (rsp - 8#64)
  let _ ← load 1 (rsp - 11#64)
  StateT.assert fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print redZoneRegs

end Ascent.Kraken.Tests.StackFrame
