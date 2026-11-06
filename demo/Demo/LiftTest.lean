import Demo.Lift

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

attribute [local ascend] wrp_bind wrp_pure_unit wrp_movRegSib8_load8 wrp_addRegSib8_load8
  wrp_movSib8Reg_store8

ascend_def liftTest1 (rsi rax : BitVec 64) : BlockM DataMem Unit from
  ⦃fun t => PureRefinement (t.regs.get64 .rsi) rsi True Eq ∧ PureRefinement (t.regs.get64 .rax) rax True Eq⦄
  (modifyIf (loadOk8 .rsi .rax 0) (movRegSib8 .r8 .rsi .rax 0) >>= fun _ => pure ()
    : BlockM MachineData Unit)
  ⪯[ofStateRepr MachineData.dmem] liftTest1 ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [] with finish

#print liftTest1

ascend_def liftTest3 (rdi rsi rdx rsp rax : BitVec 64) : BlockM DataMem Unit from
  ⦃fun t => PureRefinement (t.regs.get64 .rdi) rdi True Eq ∧ PureRefinement (t.regs.get64 .rsi) rsi True Eq ∧
    PureRefinement (t.regs.get64 .rdx) rdx True Eq ∧ PureRefinement (t.regs.get64 .rsp) rsp True Eq ∧
    PureRefinement (t.regs.get64 .rax) rax True Eq⦄
  (do
    modifyIf (loadOk8 .rsi .rax 0) (movRegSib8 .r8 .rsi .rax 0)
    modifyIf (loadOk8 .rdi .rax 0) (addRegSib8 .r8 .rdi .rax 0)
    modifyIf (storeOk8 .rdx .rax 0) (movSib8Reg .rdx .rax 0 .r8)
    pure () : BlockM MachineData Unit)
  ⪯[ofStateRepr MachineData.dmem] liftTest3 ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [] with finish

#print liftTest3

end Ascent.Kraken
