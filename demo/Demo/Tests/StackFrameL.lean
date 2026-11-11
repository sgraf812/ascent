import Demo.Lift
import Demo.Tests.StackFrame

/-!
# Stack frames with their registers lifted

Regression tests for the register layer on the leaf functions of `Demo.Tests.StackFrame`. Each
`xL₀` is `xT` over the data memory alone, synthesized by `ascend`, and `xL` instantiates the frame
parameter `r₀` with the entry value of `rsp`. The `#print` of each `xL` records the current result.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken.Tests.StackFrame

ascend_def pushPopL₀ [Host] [Embeds pushPop] (rdi rsi rbx r12 rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rbx, rbx), (.r12, r12), (.rsp, rsp)]⦄
  (pushPopT r₀ ra) ⪯[ofStateRepr MachineData.dmem] pushPopL₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [pushPopT]
  with finish

sym_simp_def pushPopL [Host] [Embeds pushPop] (rbx r12 rsp : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
    pushPopL₀ rbx r12 rsp rsp ra
  using pre [] post [stayAt_self, eq_self_iff_true, true_and, assume_true_bind, assume_true, pure_bind,
    bind_pure, pushPopL₀, bind_pure_unit, BitVec.sub_add_cancel, BitVec.ofInt_int64ToInt,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg, BitVec.ofNat_eq_ofNat, BitVec.add_neg_eq_sub]

/--
info: def Ascent.Kraken.Tests.StackFrame.pushPopL : BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rbx r12 rsp ra => do
  store 8 (rsp - 8#64) rbx
  store 8 (rsp - 8#64 - 8#64) r12
  let _ ← load 8 (rsp - 8#64 - 8#64)
  let _ ← load 8 (rsp - 8#64)
  StateT.assume fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print pushPopL

ascend_def localsL₀ [Host] [Embeds locals] (rdi rsi rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rsp, rsp)]⦄
  (localsT r₀ ra) ⪯[ofStateRepr MachineData.dmem] localsL₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [localsT]
  with finish

sym_simp_def localsL [Host] [Embeds locals] (rdi rsi rsp : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
    localsL₀ rdi rsi rsp rsp ra
  using pre [] post [stayAt_self, eq_self_iff_true, true_and, assume_true_bind, assume_true, pure_bind,
    bind_pure, localsL₀, bind_pure_unit, BitVec.sub_add_cancel, BitVec.ofInt_int64ToInt,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg, BitVec.ofNat_eq_ofNat, BitVec.add_neg_eq_sub]

/--
info: def Ascent.Kraken.Tests.StackFrame.localsL : BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rdi rsi rsp ra => do
  store 8 (rsp - 16#64 + 8#64) rdi
  store 8 (rsp - 16#64) rsi
  let _ ← load 8 (rsp - 16#64 + 8#64)
  let _ ← load 8 (rsp - 16#64)
  StateT.assume fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print localsL

ascend_def bytesL₀ [Host] [Embeds bytes] (rax rcx rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rax, rax), (.rcx, rcx), (.rsp, rsp)]⦄
  (bytesT r₀ ra) ⪯[ofStateRepr MachineData.dmem] bytesL₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [bytesT]
  with finish

sym_simp_def bytesL [Host] [Embeds bytes] (rax rsp : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
    bytesL₀ rax rsp rsp ra
  using pre [] post [stayAt_self, eq_self_iff_true, true_and, assume_true_bind, assume_true, pure_bind,
    bind_pure, bytesL₀, bind_pure_unit, BitVec.sub_add_cancel, BitVec.ofInt_int64ToInt,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg, BitVec.ofNat_eq_ofNat, BitVec.add_neg_eq_sub]

/--
info: def Ascent.Kraken.Tests.StackFrame.bytesL : BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rax rsp ra => do
  store 1 (rsp - 16#64 + 3#64) rax
  let _ ← load 1 (rsp - 16#64 + 3#64)
  let _ ← load 1 (rsp - 16#64 + 3#64)
  StateT.assume fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print bytesL

ascend_def halvesL₀ [Host] [Embeds halves] (rax rcx rdx rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rax, rax), (.rcx, rcx), (.rdx, rdx), (.rsp, rsp)]⦄
  (halvesT r₀ ra) ⪯[ofStateRepr MachineData.dmem] halvesL₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [halvesT]
  with finish

sym_simp_def halvesL [Host] [Embeds halves] (rax rsp : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
    halvesL₀ rax rsp rsp ra
  using pre [] post [stayAt_self, eq_self_iff_true, true_and, assume_true_bind, assume_true, pure_bind,
    bind_pure, halvesL₀, bind_pure_unit, BitVec.sub_add_cancel, BitVec.ofInt_int64ToInt,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg, BitVec.ofNat_eq_ofNat, BitVec.add_neg_eq_sub]

/--
info: def Ascent.Kraken.Tests.StackFrame.halvesL : BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rax rsp ra => do
  store 2 (rsp - 8#64 - 2#64) rax
  let _ ← load 2 (rsp - 8#64 - 2#64)
  store 2 (rsp - 8#64 + 5#64) rax
  let _ ← load 2 (rsp - 8#64 + 5#64)
  StateT.assume fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print halvesL

ascend_def redZoneL₀ [Host] [Embeds redZone] (rdi rax rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rax, rax), (.rsp, rsp)]⦄
  (redZoneT r₀ ra) ⪯[ofStateRepr MachineData.dmem] redZoneL₀
  ⦃fun _ _ _ => True; (fun l l' t => l = l' ∧ t.regs.get64 .rsp = r₀ + 8, estack⟨⟩)⦄
  ascend [redZoneT]
  with finish

sym_simp_def redZoneL [Host] [Embeds redZone] (rdi rax rsp : BitVec 64) (ra : Int64) :
    BlockM DataMem Unit from
    redZoneL₀ rdi rax rsp rsp ra
  using pre [] post [stayAt_self, eq_self_iff_true, true_and, assume_true_bind, assume_true, pure_bind,
    bind_pure, redZoneL₀, bind_pure_unit, BitVec.sub_add_cancel, BitVec.ofInt_int64ToInt,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg, BitVec.ofNat_eq_ofNat, BitVec.add_neg_eq_sub]

/--
info: def Ascent.Kraken.Tests.StackFrame.redZoneL : BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem Unit :=
fun rdi rax rsp ra => do
  store 8 (rsp + 18446744073709551608#64) rdi
  store 1 (rsp + 18446744073709551605#64) rax
  let _ ← load 8 (rsp + 18446744073709551608#64)
  let _ ← load 1 (rsp + 18446744073709551605#64)
  StateT.assume fun m => retAddrAt m rsp = some ra
  throw ra
-/
#guard_msgs in
#print redZoneL

end Ascent.Kraken.Tests.StackFrame
