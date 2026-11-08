import Demo.Lift

/-!
# Register lifting on a straight-line block

The loop body of `zipWithAdd` without the loop: two loads into `r8` and a store of `r8`. The
abstract program binds both loaded values and stores their sum.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken.LiftTest

ascend_def body (rdi rsi rdx rsp rax : BitVec 64) : BlockM DataMem Unit from
  ⦃fun t => t.regs.get64 .rdi ≐ rdi ∧ t.regs.get64 .rsi ≐ rsi ∧ t.regs.get64 .rdx ≐ rdx ∧
    t.regs.get64 .rsp ≐ rsp ∧ t.regs.get64 .rax ≐ rax⦄
  (do
    modifyIf (loadOk 8 (sib 8 .rsi .rax 0)) (loadReg 8 .r8 (sib 8 .rsi .rax 0) fun w _ => w)
    modifyIf (loadOk 8 (sib 8 .rdi .rax 0))
      (loadReg 8 .r8 (sib 8 .rdi .rax 0) fun w st => w + st.regs.get64 .r8)
    modifyIf (storeOk 8 (sib 8 .rdx .rax 0)) (storeWord 8 (sib 8 .rdx .rax 0) fun st => st.regs.get64 .r8)
    pure () : BlockM MachineData Unit)
  ⪯[ofStateRepr MachineData.dmem] body ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend []

example (rdi rsi rdx rsp rax : BitVec 64) : body rdi rsi rdx rsp rax = (do
    let x ← load8 (rsi + rax * 8)
    let y ← load8 (rdi + rax * 8)
    store8 rsp (rdx + rax * 8) (y + x)
    pure ()) := rfl

end Ascent.Kraken.LiftTest
