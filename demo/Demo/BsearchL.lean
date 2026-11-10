import Demo.Lift
import Demo.BsearchStruct

/-!
# The binary search with its registers lifted

`bsearchL₀` is `bsearchT` over the data memory alone, synthesized by `ascend`. The lifting relation
`RegsRel` names the registers that become values: `rdi` (the array), `rdx` (the key) and `rsp` are
parameters, `rsi` starts as the length, and the loop carries the bounds `rcx` and `rsi`. The function
returns through `ret v`, where `v` is the value of `rax` at the return.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def bsearchL₀ (rdi rsi rdx rsp : BitVec 64) : BlockM DataMem Unit from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rsp, rsp)]⦄
  bsearchT ⪯[ofStateRepr MachineData.dmem] bsearchL₀
  ⦃fun _ _ _ => True; (fun l l' t => l = .exit ∧ ∃ v, t.regs.get64 .rax ≐ v ∧ l' = .ret v, estack⟨⟩)⦄
  ascend [bsearchT, wrp_forIn_lockstep_unit (ab := (_, _)) (R := fun t (v : BitVec 64 × BitVec 64) =>
    match v with
    | (lo, hi) => RegsRel [(.rdi, rdi), (.rdx, rdx), (.rsp, rsp), (.rcx, lo), (.rsi, hi)] t)]
  with finish

sym_simp_def bsearchL (rdi rsi rdx rsp : BitVec 64) : BlockM DataMem Unit from bsearchL₀ rdi rsi rdx rsp
  using pre [] post [bsearchL₀, condState_const, CondCode.cmp_be_eq_true, CondCode.cmp_l_eq_true,
    CondCode.cmp_le_eq_true, bind_pure_unit, pure_bind, Bool.not_eq_true']

/--
info: def Ascent.Kraken.bsearchL : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BlockM DataMem Unit :=
fun rdi rsi rdx rsp => do
  let mut a := (0#64, rsi)
  repeat'
    if a.snd ≤ a.fst then 
      StateT.assume fun m => (Mem.loadInt m rsp 8).isSome = true
      throw (CfgLabel.ret 18446744073709551615#64)
    else
      let x ← load 8 (rdi + (a.fst + (a.snd - a.fst).ushiftRight 1) * 8#64)
      if x.toInt < rdx.toInt then 
        a := (a.fst + (a.snd - a.fst).ushiftRight 1 + 1#64, a.snd)
      else
        if x.toInt ≤ rdx.toInt then 
          StateT.assume fun m => (Mem.loadInt m rsp 8).isSome = true
          throw (CfgLabel.ret (a.fst + (a.snd - a.fst).ushiftRight 1))
        else
          a := (a.fst, a.fst + (a.snd - a.fst).ushiftRight 1)
-/
#guard_msgs in
#print bsearchL

theorem bsearchL.refines (rdi rsi rdx rsp : BitVec 64) :
    ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rsp, rsp)]⦄
      bsearchT ⪯[ofStateRepr MachineData.dmem] (bsearchL rdi rsi rdx rsp)
      ⦃fun _ _ _ => True; (fun l l' t => l = .exit ∧ ∃ v, t.regs.get64 .rax ≐ v ∧ l' = .ret v, estack⟨⟩)⦄ :=
  bsearchL.eq rdi rsi rdx rsp ▸ bsearchL₀.refines rdi rsi rdx rsp

end Ascent.Kraken
