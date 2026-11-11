import Demo.Lift
import Demo.BsearchStruct

/-!
# The binary search with its registers lifted

`bsearchL₀` is `bsearchT` over the data memory alone, synthesized by `ascend`. The lifting relation
`RegsRel` names the registers that become values: `rdi` (the array), `rdx` (the key) and `rsp` are
parameters, `rsi` starts as the length, and the loop carries the bounds `rcx` and `rsi` and the
result register `rax`. The concrete program is `bsearchR`, in which the return leaves the loop, and
the abstract program returns the value of `rax`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Kraken

ascend_def bsearchL₀ (rdi rsi rdx rax rsp : BitVec 64) (r₀ : BitVec 64) (ra : Int64) : BlockM DataMem (BitVec 64) from
  ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rax, rax), (.rsp, rsp)]⦄
  (bsearchR r₀ ra) ⪯[ofStateRepr MachineData.dmem] bsearchL₀
  ⦃fun _ v t => t.regs.get64 .rax ≐ v ∧ t.regs.get64 .rsp = r₀ + 8;
    (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [bsearchR, wrp_forIn_lockstep_pure
    (fun _ t (v : BitVec 64 × BitVec 64 × BitVec 64) => match v with
      | (lo, hi, res) => RegsRel [(.rdi, rdi), (.rdx, rdx), (.rsp, rsp), (.rcx, lo), (.rsi, hi), (.rax, res)] t)
    (fun _ t (v : BitVec 64 × BitVec 64 × BitVec 64) => match v with
      | (lo, hi, res) => RegsRel [(.rcx, lo), (.rsi, hi), (.rax, res)] t ∧
          t.regs.get64 .rsp = r₀ + 8) _ (_, _, _)]
  with finish

sym_simp_def bsearchL (rdi rsi rdx rax : BitVec 64) (rsp : BitVec 64) (ra : Int64) : BlockM DataMem (BitVec 64) from
    bsearchL₀ rdi rsi rdx rax rsp rsp ra
  using pre [] post [stayAt_self, eq_self_iff_true, true_and, assume_true_bind, assume_true, pure_bind, bind_pure, bsearchL₀, condState_const, CondCode.cmp_be_eq_true, CondCode.cmp_l_eq_true,
    CondCode.cmp_le_eq_true, bind_pure_unit, pure_bind, Bool.not_eq_true']


theorem bsearchL.refines (rdi rsi rdx rax : BitVec 64) (rsp : BitVec 64) (ra : Int64) :
    ⦃RegsRel [(.rdi, rdi), (.rsi, rsi), (.rdx, rdx), (.rax, rax), (.rsp, rsp)]⦄
      (bsearchR rsp ra) ⪯[ofStateRepr MachineData.dmem] (bsearchL rdi rsi rdx rax rsp ra)
      ⦃fun _ v t => t.regs.get64 .rax ≐ v ∧ t.regs.get64 .rsp = rsp + 8;
        (fun l l' _ => l = l', estack⟨⟩)⦄ :=
  bsearchL.eq rdi rsi rdx rax rsp ra ▸ bsearchL₀.refines rdi rsi rdx rax rsp rsp ra

/--
info: def Ascent.Kraken.bsearchL : BitVec 64 →
  BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Int64 → BlockM DataMem (BitVec 64) :=
fun rdi rsi rdx rax rsp ra => do
  let mut a := (0#64, rsi, rax)
  repeat'
    if a.snd.fst ≤ a.fst then 
      StateT.assume fun m => retAddrAt m rsp = some ra
      a := (a.fst, a.snd.fst, 18446744073709551615#64)
      break
    else
      let x ← load 8 (rdi + (a.fst + (a.snd.fst - a.fst).ushiftRight 1) * 8#64)
      if x.toInt < rdx.toInt then 
        a := (a.fst + (a.snd.fst - a.fst).ushiftRight 1 + 1#64, a.snd.fst, a.snd.snd)
      else
        if x.toInt ≤ rdx.toInt then 
          StateT.assume fun m => retAddrAt m rsp = some ra
          a := (a.fst, a.snd.fst, a.fst + (a.snd.fst - a.fst).ushiftRight 1)
          break
        else
          a := (a.fst, a.fst + (a.snd.fst - a.fst).ushiftRight 1, a.snd.snd)
  pure a.snd.snd
-/
#guard_msgs in
#print bsearchL

end Ascent.Kraken
