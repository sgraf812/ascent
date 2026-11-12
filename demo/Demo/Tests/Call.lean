import Demo.L1Rel
import Demo.Swap

/-!
# A call at the first layer

`caller` calls `_swap` and returns. Under `JRel Mem.Sub`, the call becomes `withRa k` for the
abstract program `k` of the callee, given as a hypothesis together with the declaration of `_swap`.
`swapR` is `swap` under the same relation, synthesized with the rules of `Demo.L1Gen`.
-/
open Kraken.X64.Parser Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRel)
open scoped Program.WP
set_option experimental.vcgen true
namespace Ascent.Kraken.Tests.Call
attribute [local vcgen_simp] swap

ascend_def swapR [Host] [FunDecls] [Embeds swap] (r₀ : BitVec 64) (ra : Int64) :
    BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ swap ⪯[ofStateRel (JRel Mem.Sub)] swapR
    ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  ascend [refines_cfg_rel (JRel Mem.Sub) (fun _ _ h => JRel.regs h) (p := swap)] with finish

def caller : Program := parse("
_caller:
  callq _swap
  retq
")
attribute [local vcgen_simp] caller

ascend_def callerA [Host] [FunDecls] [Embeds caller] (g : Fragment) (hg : FunDecls.at (label "_swap") = some g)
    (k : BitVec 64 → Int64 → BlockM MachineData Unit)
    (hk : ∀ r₀ ra, ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ g.prog
      ⪯[ofStateRel (JRel Mem.Sub)] (k r₀ ra) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄)
    (r₀ : BitVec 64) (ra : Int64) : BlockM MachineData Unit from
  ⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ caller ⪯[ofStateRel (JRel Mem.Sub)] callerA
    ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄
  ascend [refines_cfg_rel (JRel Mem.Sub) (fun _ _ h => JRel.regs h) (p := caller), wrp_call_withRa hg _ _ hk]
    with finish
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
          withRa k
          exitIf (retOk r₀ ra) (setReg64 Reg64.rsp fun x => r₀ + 8) ra)])
-/
#guard_msgs in
#print callerA
end Ascent.Kraken.Tests.Call
