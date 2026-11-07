import Demo.ZipPure

/-!
# From x64 to `Array.zipWith`

The C function

```c
void zipWithAdd(const long *a, const long *b, long *out, long n) {
  for (long i = 0; i < n; i++)
    out[i] = a[i] + b[i];
}
```

compiled by clang with `-O1 -fno-vectorize -fno-unroll-loops` is the kraken program `zipWithAdd`.
Each section below is one refinement, from the machine code to the pure program.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open StateT (assume)
open scoped Program.WP

namespace Ascent.Kraken.Walkthrough

/-! ## 1. The x64 text -/

#print zipWithAdd

/-! ## 2. Blocks, synthesized by `ascend_def`

`zipWithAddA` is a loop over the blocks of the text, one guarded step per instruction, with the flags
cleared and `cmp; jcc` fused into one branch. Each step is a register write `setReg64`, a load into a
register `loadReg8`, or a store `storeWord8`. `ascend_def` synthesized it and proved: -/

/--
info: @zipWithAddA.refines : ∀ [inst : Host] [inst_1 : FunDecls] [inst_2 : Embeds zipWithAdd] (s : MachineData) (ra : Int64),
  Refinement zipWithAdd (zipWithAddA s ra) (ofStateRepr abs) (fun x => x = s.push64 ra) (fun x x_1 => ⊤) (RetRel s ra)
-/
#guard_msgs in
#check @zipWithAddA.refines

/-! ## 3. A structured loop, by rewriting

`sym_simp_def` rewrites the block loop of `zipWithAddA` into an `if` and a `repeat'` loop over the
machine state: the jump of the loop block to itself becomes `continue`, and the return ends the
program in both branches. The command proves
the equation `zipWithAddT.eq`, so the first refinement carries over to `zipWithAddT`: -/

/--
info: def Ascent.Kraken.zipWithAddT : [inst : Host] →
  [FunDecls] → [Embeds zipWithAdd] → MachineData → Int64 → BlockM MachineData Unit :=
fun [Host] [FunDecls] [Embeds zipWithAdd] s ra =>
  condState (fun st => CondCode.le.cmp (st.regs.rcx.toBitVec &&& st.regs.rcx.toBitVec) 0#64)
    (exitIf (loadOk8 fun st => st.regs.rsp.toBitVec) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
      CfgLabel.exit)
    do
    modifyIf (fun x => True) (setReg64 Reg64.rax fun st => 0#64)
    { }.forIn PUnit.unit fun x x_1 => do
        modifyIf (loadOk8 (sib8 Reg64.rsi Reg64.rax 0)) (loadReg8 Reg64.r8 (sib8 Reg64.rsi Reg64.rax 0) fun w x => w)
        modifyIf (loadOk8 (sib8 Reg64.rdi Reg64.rax 0))
            (loadReg8 Reg64.r8 (sib8 Reg64.rdi Reg64.rax 0) fun w st => w + st.regs.r8.toBitVec)
        modifyIf (storeOk8 (sib8 Reg64.rdx Reg64.rax 0))
            (storeWord8 (sib8 Reg64.rdx Reg64.rax 0) fun st => st.regs.r8.toBitVec)
        modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.rax.toBitVec + 1#64)
        condState (fun st => CondCode.nz.cmp st.regs.rcx.toBitVec st.regs.rax.toBitVec)
            (pure (ForInStep.yield PUnit.unit))
            (exitIf (loadOk8 fun st => st.regs.rsp.toBitVec) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
              CfgLabel.exit)
-/
#guard_msgs in
#print zipWithAddT
/--
info: @zipWithAddT.refines : ∀ [inst : Host] [inst_1 : FunDecls] [inst_2 : Embeds zipWithAdd] (s : MachineData) (ra : Int64),
  Refinement zipWithAdd (zipWithAddT s ra) (ofStateRepr abs) (fun x => x = s.push64 ra) (fun x x_1 => ⊤) (RetRel s ra)
-/
#guard_msgs in
#check @zipWithAddT.refines

/-! ## 4. Registers as values, synthesized by `ascend_def`

The state is the data memory alone. The lifting relation, the one hint of the run, is
`RegsRel [(.rdi, rdi), …, (.rax, rax)]`: it names the registers that become values. `rdi`, `rsi`,
`rdx`, `rcx` and `rsp` are parameters, and `rax` is the value of the loop. The loaded values of
`r8` become variables. `ascend_def` synthesized `zipWithAddL₀`, and `sym_simp_def` states its
branch conditions as comparisons of the values in `zipWithAddL`. The return is an `assume` that the
return slot is mapped, followed by `throw CfgLabel.exit`: -/

/--
info: def Ascent.Kraken.zipWithAddL : [inst : Host] →
  [FunDecls] →
    [Embeds zipWithAdd] →
      MachineData → Int64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BlockM DataMem Unit :=
fun [Host] [FunDecls] [Embeds zipWithAdd] s ra rdi rsi rdx rcx rsp =>
  if rcx.toInt ≤ 0 then do
    assume fun m => (Mem.loadInt m rsp 8).isSome = true
    throw CfgLabel.exit
  else do
    let mut v := 0#64
    repeat'
      let x ← load8 (rsi + v * 8#64)
      let x_1 ← load8 (rdi + v * 8#64)
      store8 rsp (rdx + v * 8#64) (x_1 + x)
      if ¬rcx = v + 1#64 then 
        v := v + 1#64
      else
        assume fun m => (Mem.loadInt m rsp 8).isSome = true
        throw CfgLabel.exit
    pure PUnit.unit
-/
#guard_msgs in
#print zipWithAddL
/--
info: @zipWithAddL.refines : ∀ [inst : Host] [inst_1 : FunDecls] [inst_2 : Embeds zipWithAdd] (s : MachineData) (ra : Int64)
  (rdi rsi rdx rcx rsp : BitVec 64),
  Refinement (zipWithAddT s ra) (zipWithAddL s ra rdi rsi rdx rcx rsp) (ofStateRepr MachineData.dmem)
    (RegsRel [(Reg64.rdi, rdi), (Reg64.rsi, rsi), (Reg64.rdx, rdx), (Reg64.rcx, rcx), (Reg64.rsp, rsp)])
    (fun x x_1 x_2 => True) estack⟨fun l l' x => l = l'⟩
-/
#guard_msgs in
#check @zipWithAddL.refines

/-! ## 5. Arrays, synthesized by `ascend_def`

The state is the output array. The input arrays are parameters, named by their base addresses, and
the loads and the store become array reads and an array update. The words that count become
numbers: the loop counter `v` of `zipWithAddL` holds the number `i` (`v ≐ₙ i`), the length `rcx`
holds `n`, and the comparisons of the words become comparisons of the numbers. The relation of the
loop, the hint of the run, states `v ≐ₙ i`, the bound `i < n`, and the layout
`ArrayLayout [(A, a), (B, b)] O n [rsp]` of the memory: the input arrays, the written array, and the
return slot. `ascend_def` synthesized `zipWithAddArr₀`, and `sym_simp_def` puts the array reads in
place and states the conditions as propositions in `zipWithAddArr`: -/

/--
info: def Ascent.Kraken.zipWithAddArr : [inst : Host] →
  [FunDecls] →
    [Embeds zipWithAdd] →
      MachineData →
        Int64 →
          BitVec 64 →
            BitVec 64 →
              BitVec 64 → BitVec 64 → Nat → Array (BitVec 64) → Array (BitVec 64) → BlockM (Array (BitVec 64)) Unit :=
fun [Host] [FunDecls] [Embeds zipWithAdd] s ra A B O rsp n a b =>
  if n = 0 then throw CfgLabel.exit
  else do
    let mut i := 0
    repeat'
      modify fun o => o.set! i (a[i]! + b[i]!)
      if ¬n = i + 1 then 
        i := i + 1
      else
        throw CfgLabel.exit
    pure PUnit.unit
-/
#guard_msgs in
#print zipWithAddArr
/--
info: @zipWithAddArr.refines : ∀ [inst : Host] [inst_1 : FunDecls] [inst_2 : Embeds zipWithAdd] (s : MachineData) (ra : Int64)
  (A B O rsp : BitVec 64) (n : Nat) (a b : Array (BitVec 64)),
  Refinement (zipWithAddL s ra A B O (BitVec.ofNat 64 n) rsp) (zipWithAddArr s ra A B O rsp n a b)
    (ofStateRepr (outView O n))
    (fun m => A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout [(A, a), (B, b)] O n [rsp] m)
    (fun x x_1 x_2 => True) estack⟨fun l l' x => l = l'⟩
-/
#guard_msgs in
#check @zipWithAddArr.refines

/-! ## 6. The pure program

`vcgen` proves that the array program exits with `Array.zipWith (· + ·)` of its inputs, from a loop
invariant and a measure. `ascend_def` takes this result as the premise of `wrp_purify_throw` and
synthesizes the pure program: -/

/--
info: @zipWithAddArr_spec : ∀ [inst : Host] [inst_1 : FunDecls] [inst_2 : Embeds zipWithAdd] (s : MachineData) (ra : Int64)
  (A B O rsp : BitVec 64) {n : Nat} {a b : Array (BitVec 64)},
  a.size = n →
    b.size = n →
      ⦃ fun x => x.size = n ⦄ zipWithAddArr s ra A B O rsp n a b ⦃ fun x x_1 => False;
        estack⟨fun l o' => l = CfgLabel.exit ∧ o' = Array.zipWith (fun x1 x2 => x1 + x2) a b⟩ ⦄
-/
#guard_msgs in
#check @zipWithAddArr_spec
/--
info: def Ascent.Kraken.zipWithAddP : [inst : Host] →
  [FunDecls] →
    [Embeds zipWithAdd] →
      MachineData →
        Int64 →
          BitVec 64 →
            BitVec 64 →
              BitVec 64 →
                BitVec 64 → (n : Nat) → (a b : Array (BitVec 64)) → a.size = n → b.size = n → Id (Array (BitVec 64)) :=
fun [Host] [FunDecls] [Embeds zipWithAdd] s ra A B O rsp n a b ha hb => pure (Array.zipWith HAdd.hAdd a b)
-/
#guard_msgs in
#print zipWithAddP

/-! ## 7. Back to the machine code

`Refinement.comp_le` composes the refinements of the layers into one refinement from the x64 text to
the pure program: -/

#check @zipWithAdd_refines_P

/-! One `Refinement.transport` of this refinement, and the reading of the output array as memory
words, give the result on the machine code: -/

/--
info: @zipWithAdd_correct : ∀ [inst : Host] [inst_1 : FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64)
  {A B O : BitVec 64} {n : Nat},
  (s.push64 ra).regs.get64 Reg64.rdi = A →
    (s.push64 ra).regs.get64 Reg64.rsi = B →
      (s.push64 ra).regs.get64 Reg64.rdx = O →
        (s.push64 ra).regs.get64 Reg64.rcx = BitVec.ofNat 64 n →
          ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 Reg64.rsp) n →
            ⦃ fun t => t = s.push64 ra ⦄ zipWithAdd ⦃ fun x x_1 => True; fun a t =>
              a = ra ∧
                t.regs.get64 Reg64.rsp = s.regs.get64 Reg64.rsp ∧
                  words t.dmem O n =
                    List.zipWith (fun x1 x2 => x1 + x2) (words (s.push64 ra).dmem A n) (words (s.push64 ra).dmem B n) ⦄
-/
#guard_msgs in
#check @zipWithAdd_correct
#print axioms zipWithAdd_correct

end Ascent.Kraken.Walkthrough
