import Demo.L1Rel
import Demo.Swap

/-!
# A call at the instruction layer

`caller` calls `_swap` and returns. The call becomes `callA` of the abstract callee `k`, given as a
hypothesis together with the declaration of `_swap`, and the refinement of `swap` has the shape of
that hypothesis. Two calls in sequence are defined: a call pushes an unknown word into the return
slot, so the slot stays mapped for the next call.
-/

open Kraken.X64.Parser Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRel)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken.Tests.Call

def caller : Program := parse("
_caller:
  callq _swap
  retq
")

attribute [local vcgen_simp] caller

ascend_def callerA [Host] [FunDecls] [Embeds caller] (g : Fragment) (hg : FunDecls.at (label "_swap") = some g)
    (k : BitVec 64 → Int64 → BlockM MachineData Unit)
    (hk : ∀ (r : BitVec 64) (ra : Int64),
      ⦃fun s => s.regs.get64 .rsp = r ∧ s.retAddr = some ra⦄ g.prog ⪯[ofStateRepr abs] (k r ra)
        ⦃fun _ _ => ⊤; AddrRel r ra⦄)
    (r₀ : BitVec 64) (ra : Int64) : BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ caller ⪯[ofStateRepr abs] callerA
    ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  ascend [refines_cfg (p := caller) (habs := abs_regs), wrp_call hg _ _ hk] with finish

/--
info: def Ascent.Kraken.Tests.Call.callerA : [Host] →
  (BitVec 64 → Int64 → BlockM MachineData Unit) → BitVec 64 → Int64 → BlockM MachineData Unit :=
fun [Host] k r₀ ra =>
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
          callA k
          exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8) ra)])
-/
#guard_msgs in
#print callerA

-- The refinement of `swap` is the premise of the call rule for the callee `swapA`.
example [Host] [FunDecls] [Embeds swap] :
    ∀ (r : BitVec 64) (ra : Int64),
      ⦃fun s => s.regs.get64 .rsp = r ∧ s.retAddr = some ra⦄ (⟨swap⟩ : Fragment).prog
        ⪯[ofStateRepr abs] (swapA r ra) ⦃fun _ _ => ⊤; AddrRel r ra⦄ :=
  fun r ra => swapA.refines r ra

/-! ## Two calls in sequence

A call pushes an unknown word into the return slot, so the slot is mapped for the next call at the
same stack pointer. -/

noncomputable def retK (r : BitVec 64) (ra : Int64) : BlockM MachineData Unit := do
  modifyIf (fun _ => True) (setReg64 .rsp fun _ => r + 8#64)
  throw ra

example (s : MachineData) (h : (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true) :
    wp (callA retK >>= fun _ => callA retK) (fun _ _ => True) (fun _ _ => True, estack⟨⟩) s := by
  simp only [callA, retK, WPMonadExact.wp_bind_eq, wp_peek, BlockLoop.wp_tryCatch, wp_modifyIf_fun,
    wp_pushUnknown_fun, wp_throw_block]
  simpa [setReg64, MachineData.push64, BitVec.sub_add_cancel, Mem.loadInt_storeInt_64] using h

end Ascent.Kraken.Tests.Call
