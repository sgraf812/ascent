import Demo.ZipBinary

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

/--
info: def zipWithAdd : Program :=
[asm|
    "test rcx, rcx"
    "jle LBB0_3"
    "xor eax, eax"
    "LBB0_2:"
    "mov r8, QWORD PTR [rsi+rax*8+0]"
    "add r8, QWORD PTR [rdi+rax*8+0]"
    "mov QWORD PTR [rdx+rax*8+0], r8"
    "inc rax"
    "cmp rcx, rax"
    "jne LBB0_2"
    "LBB0_3:"
    "ret"]
-/
#guard_msgs in
#print zipWithAdd

/-! ## 2. Blocks, synthesized by `ascend_def`

`zipWithAddA` is a loop over the blocks of the text, one guarded step per instruction, with the flags
cleared and `cmp; jcc` fused into one branch. Each step is a register write `setReg64`, a load into a
register `loadReg 8`, or a store `storeWord 8`. `ascend_def` synthesized it and proved: -/

/--
info: @zipWithAddA.refines : ∀ [inst : Host] [inst_1 : FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64),
  ⦃ fun x => x = s.push64 ra ⦄ zipWithAdd ⪯[ofStateRepr abs] zipWithAddA ⦃ fun x x_1 => ⊤; RetRel s ra ⦄
-/
#guard_msgs in
#check @zipWithAddA.refines

/-! ## 3. A structured loop, by rewriting

`sym_simp_def` rewrites the block loop of `zipWithAddA` into an `if` and a `repeat'` loop over the
machine state: the jump of the loop block to itself becomes `continue`, and the return ends the
program in both branches. The command proves
the equation `zipWithAddT.eq`, so the first refinement carries over to `zipWithAddT`: -/

/--
info: def Ascent.Kraken.zipWithAddT : BlockM MachineData Unit :=
condState (fun st => CondCode.le.cmp (st.regs.rcx.toBitVec &&& st.regs.rcx.toBitVec) 0#64)
  (exitIf (loadOk 8 fun st => st.regs.rsp.toBitVec) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
    CfgLabel.exit)
  do
  modifyIf (fun x => True) (setReg64 Reg64.rax fun st => 0#64)
  { }.forIn PUnit.unit fun x x_1 => do
      modifyIf (loadOk 8 (sib 8 Reg64.rsi Reg64.rax 0)) (loadReg 8 Reg64.r8 (sib 8 Reg64.rsi Reg64.rax 0) fun w x => w)
      modifyIf (loadOk 8 (sib 8 Reg64.rdi Reg64.rax 0))
          (loadReg 8 Reg64.r8 (sib 8 Reg64.rdi Reg64.rax 0) fun w st => w + st.regs.r8.toBitVec)
      modifyIf (storeOk 8 (sib 8 Reg64.rdx Reg64.rax 0))
          (storeWord 8 (sib 8 Reg64.rdx Reg64.rax 0) fun st => st.regs.r8.toBitVec)
      modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.rax.toBitVec + 1#64)
      condState (fun st => CondCode.nz.cmp st.regs.rcx.toBitVec st.regs.rax.toBitVec)
          (pure (ForInStep.yield PUnit.unit))
          (exitIf (loadOk 8 fun st => st.regs.rsp.toBitVec) (setReg64 Reg64.rsp fun st => st.regs.rsp.toBitVec + 8#64)
            CfgLabel.exit)
-/
#guard_msgs in
#print zipWithAddT
/--
info: @zipWithAddT.refines : ∀ [inst : Host] [inst_1 : FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64),
  ⦃ fun x => x = s.push64 ra ⦄ zipWithAdd ⪯[ofStateRepr abs] zipWithAddT ⦃ fun x x_1 => ⊤; RetRel s ra ⦄
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
info: def Ascent.Kraken.zipWithAddL : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BlockM DataMem Unit :=
fun rdi rsi rdx rcx rsp =>
  if rcx.toInt ≤ 0 then do
    assume fun m => (Mem.loadInt m rsp 8).isSome = true
    throw CfgLabel.exit
  else do
    let mut v := 0#64
    repeat'
      let x ← load 8 (rsi + v * 8#64)
      let x_1 ← load 8 (rdi + v * 8#64)
      store 8 rsp (rdx + v * 8#64) (x_1 + x)
      if ¬rcx = v + 1#64 then 
        v := v + 1#64
      else
        assume fun m => (Mem.loadInt m rsp 8).isSome = true
        throw CfgLabel.exit
-/
#guard_msgs in
#print zipWithAddL
/--
info: zipWithAddL.refines : ∀ (rdi rsi rdx rcx rsp : BitVec 64),
  ⦃ RegsRel [(Reg64.rdi, rdi), (Reg64.rsi, rsi), (Reg64.rdx, rdx), (Reg64.rcx, rcx), (Reg64.rsp, rsp)] ⦄
    zipWithAddT ⪯[ofStateRepr MachineData.dmem] (zipWithAddL rdi rsi rdx rcx rsp) ⦃ fun x x_1 x_2 => True;
    estack⟨fun l l' x => l = l'⟩ ⦄
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
info: def Ascent.Kraken.zipWithAddArr : Nat → Array (BitVec 64) → Array (BitVec 64) → BlockM (Array (BitVec 64)) Unit :=
fun n a b =>
  if n = 0 then throw CfgLabel.exit
  else do
    let mut i := 0
    repeat'
      modify fun o => o.set! i (a[i]! + b[i]!)
      if ¬n = i + 1 then 
        i := i + 1
      else
        throw CfgLabel.exit
-/
#guard_msgs in
#print zipWithAddArr
/--
info: zipWithAddArr.refines : ∀ (A B O rsp : BitVec 64) (n : Nat) (a b : Array (BitVec 64)),
  ⦃ fun m => A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout [(A, a), (B, b)] O n [rsp] m ⦄
    (zipWithAddL A B O (BitVec.ofNat 64 n) rsp) ⪯[ofStateRepr (outView O n)] (zipWithAddArr n a b) ⦃ fun x x_1 x_2 =>
    True; estack⟨fun l l' x => l = l'⟩ ⦄
-/
#guard_msgs in
#check @zipWithAddArr.refines

/-! ## 6. The pure program

`vcgen` proves that the array program exits with `Array.zipWith (· + ·)` of its inputs, from a loop
invariant and a measure. `ascend_def` takes this result as the premise of `wrp_purify_throw` and
synthesizes the pure program: -/

/--
info: @zipWithAddArr_spec : ∀ {n : Nat} {a b : Array (BitVec 64)},
  a.size = n →
    b.size = n →
      ⦃ fun x => x.size = n ⦄ zipWithAddArr n a b ⦃ fun x x_1 => False;
        estack⟨fun l o' => l = CfgLabel.exit ∧ o' = Array.zipWith (fun x1 x2 => x1 + x2) a b⟩ ⦄
-/
#guard_msgs in
#check @zipWithAddArr_spec
/--
info: def Ascent.Kraken.zipWithAddP : Array (BitVec 64) → Array (BitVec 64) → Id (Array (BitVec 64)) :=
fun a b => pure (Array.zipWith HAdd.hAdd a b)
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

/-! ## 8. Bonus: the bytes

`zipWithAddBinary` is a plain `ByteArray`: the 28 bytes of machine code that the assembler emits for
the text. The loader maps every binary at `Binary.base`. The semantics of a binary fetches and
decodes one instruction at the program counter and runs kraken's semantics of that instruction.
`Binary.Assembles zipWithAdd zipWithAddBinary` states that the host lays out the text from
`Binary.base` and that the bytes at every address decode to the instruction of the text there. Under
that hypothesis the binary refines the text: -/

#check @Binary.refines_program
#check @zipWithAddBinary_refines_zipWithAdd

/-! Composed with the chain of refinements, the result holds for the bytes of every host that
assembles the text to them: -/

#check @zipWithAddBinary_correct

/-! `Binary.check` walks the text, the sizes and the bytes in one pass. One evaluation of it builds
the host `zipWithAddHost` and proves that it assembles the text to the bytes, which gives the
statement without a host: -/

#check @Binary.assembles_of_check
#check zipWithAddBinary_check
#check @zipWithAddHost_assembles
#check @zipWithAddHost_correct
#print axioms zipWithAddHost_correct

end Ascent.Kraken.Walkthrough
