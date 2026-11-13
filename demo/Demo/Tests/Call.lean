import Demo.L1Rel
import Demo.Swap

/-!
# A call at the first layer

The relation `JRel (Mem.SubSlots P)` hides the return slots `P` from the abstract state. `swapS` is
`swap` under it: its return assumes the stack pointer of the frame and throws the label `L`, and
nothing in it reads the return address. `caller` calls `_swap` and returns; the call becomes
`callA` of the abstract callee `k`, given as a hypothesis together with the declaration of `_swap`.
-/

open Kraken.X64.Parser Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRel)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken.Tests.Call

attribute [local vcgen_simp] swap

ascend_def swapS [Host] [FunDecls] [Embeds swap] (P : DataMem) (r₀ : BitVec 64) (ra L : Int64)
    (hP : (P.loadInt r₀ 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some ra) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀⦄ swap ⪯[ofStateRel (JRel (Mem.SubSlots P))] swapS
    ⦃fun _ _ => ⊤; RetExit r₀ ra L⦄
  ascend [refines_cfg_exit (JRel (Mem.SubSlots P)) (fun _ _ h => JRel.regs h) (RetExit r₀ ra L)
    (fun _ _ _ h hs => retExit_stay h hs) (p := swap), wrp_ret_slots hP, wrp_ret_slots_cons hP] with finish

/--
info: def Ascent.Kraken.Tests.Call.swapS : [Host] → BitVec 64 → Int64 → BlockM MachineData Unit :=
fun [Host] r₀ L =>
  Program.loop swap r₀
    (Table.get
      [({ label := none, idx := 0, body := [], next := some "_swap" }.label, pure PUnit.unit),
        ({ label := some "_swap", idx := 1,
              body :=
                [asm|
                    "mov rax, QWORD PTR [rdi+0]"
                    "mov rcx, QWORD PTR [rsi+0]"
                    "mov QWORD PTR [rdi+0], rcx"
                    "mov QWORD PTR [rsi+0], rax"
                    "ret"],
              next := none }.label,
          do
          modifyIf (loadOk 8 fun st => st.regs.get64 Reg64.rdi + BitVec.ofInt 64 (Int64.toInt 0))
              (loadReg 8 Reg64.rax (fun st => st.regs.get64 Reg64.rdi + BitVec.ofInt 64 (Int64.toInt 0)) fun w x => w)
          modifyIf (loadOk 8 fun st => st.regs.get64 Reg64.rsi + BitVec.ofInt 64 (Int64.toInt 0))
              (loadReg 8 Reg64.rcx (fun st => st.regs.get64 Reg64.rsi + BitVec.ofInt 64 (Int64.toInt 0)) fun w x => w)
          modifyIf (storeOk 8 fun st => st.regs.get64 Reg64.rdi + BitVec.ofInt 64 (Int64.toInt 0))
              (storeWord 8 (fun st => st.regs.get64 Reg64.rdi + BitVec.ofInt 64 (Int64.toInt 0)) fun st =>
                st.regs.get64 Reg64.rcx)
          modifyIf (storeOk 8 fun st => st.regs.get64 Reg64.rsi + BitVec.ofInt 64 (Int64.toInt 0))
              (storeWord 8 (fun st => st.regs.get64 Reg64.rsi + BitVec.ofInt 64 (Int64.toInt 0)) fun st =>
                st.regs.get64 Reg64.rax)
          exitIf (fun s => s.regs.get64 Reg64.rsp = r₀) (setReg64 Reg64.rsp fun x => r₀ + 8#64) L)])
-/
#guard_msgs in
#print swapS

def caller : Program := parse("
_caller:
  callq _swap
  retq
")

attribute [local vcgen_simp] caller

ascend_def callerS [Host] [FunDecls] [Embeds caller] (g : Fragment) (hg : FunDecls.at (label "_swap") = some g)
    (k : BitVec 64 → Int64 → BlockM MachineData Unit)
    (hk : ∀ (P' : DataMem) (r₀ : BitVec 64) (ra : Int64),
      (P'.loadInt r₀ 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some ra →
      ⦃fun s => s.regs.get64 .rsp = r₀⦄ g.prog ⪯[ofStateRel (JRel (Mem.SubSlots P'))] (k r₀ 0)
        ⦃fun _ _ => ⊤; RetExit r₀ ra 0⦄)
    (P : DataMem) (r₀ : BitVec 64) (ra L : Int64)
    (hP : (P.loadInt r₀ 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some ra) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀⦄ caller ⪯[ofStateRel (JRel (Mem.SubSlots P))] callerS
    ⦃fun _ _ => ⊤; RetExit r₀ ra L⦄
  ascend [refines_cfg_exit (JRel (Mem.SubSlots P)) (fun _ _ h => JRel.regs h) (RetExit r₀ ra L)
    (fun _ _ _ h hs => retExit_stay h hs) (p := caller), wrp_ret_slots hP, wrp_ret_slots_cons hP,
    wrp_call_slots hg _ _ 0 hk] with finish

/--
info: def Ascent.Kraken.Tests.Call.callerS : [Host] →
  (BitVec 64 → Int64 → BlockM MachineData Unit) → BitVec 64 → Int64 → BlockM MachineData Unit :=
fun [Host] k r₀ L =>
  Program.loop caller r₀
    (Table.get
      [({ label := none, idx := 0, body := [], next := some "_caller" }.label, pure PUnit.unit),
        ({ label := some "_caller", idx := 1,
              body :=
                [asm|
                    "call _swap"
                    "ret"],
              next := none }.label,
          do
          callA fun r => k r 0
          exitIf (fun s => s.regs.get64 Reg64.rsp = r₀) (setReg64 Reg64.rsp fun x => r₀ + 8#64) L)])
-/
#guard_msgs in
#print callerS

/-- The refinement of `swap` is the premise of the call rule for the callee `swapS`. -/
example [Host] [FunDecls] [Embeds swap] :
    ∀ (P' : DataMem) (r₀ : BitVec 64) (ra : Int64),
      (P'.loadInt r₀ 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some ra →
      ⦃fun s => s.regs.get64 .rsp = r₀⦄ (⟨swap⟩ : Fragment).prog
        ⪯[ofStateRel (JRel (Mem.SubSlots P'))] (swapS r₀ 0) ⦃fun _ _ => ⊤; RetExit r₀ ra 0⦄ :=
  fun P' r₀ ra hP => swapS.refines P' r₀ ra 0 hP

/-! ## Two calls in sequence

On return, `callA` leaves an unknown word in the return slot. The slot is then mapped again, and a
second call at the same stack pointer is defined. -/

noncomputable def retK (r₀ : BitVec 64) : BlockM MachineData Unit := do
  modifyIf (fun _ => True) (setReg64 .rsp fun _ => r₀ + 8#64)
  throw 0

example (s : MachineData) (h : (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true) :
    wp (callA retK >>= fun _ => callA retK) (fun _ _ => True) (fun _ _ => True, estack⟨⟩) s := by
  simp only [callA, retK, WPMonadExact.wp_bind_eq, wp_peek, BlockLoop.wp_tryCatch, wp_modifyIf_fun,
    wp_havocSlotA_fun, wp_throw_block]
  refine ⟨h, trivial, ?_, fun v => ⟨?_, trivial, ?_, fun _ => trivial⟩⟩ <;>
    simp [setReg64, hidePush, BitVec.sub_add_cancel, Mem.loadInt_storeInt_64]

end Ascent.Kraken.Tests.Call
