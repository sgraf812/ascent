import Demo.ZipBinary
import Demo.MemmovePure
import Demo.BsearchPure

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

/--
info: def zipWithAddA : BlockM MachineData Unit :=
cfgLoop
  (zipWithAdd.table
    (Table.get
      [(CfgLabel.ofLabel
            { label := none, idx := 0,
                body :=
                  [asm|
                      "test rcx, rcx"
                      "jle LBB0_3"
                      "xor eax, eax"],
                next := some "LBB0_2" }.label,
          do
          branch (fun st => CondCode.le.cmp (st.regs.get64 Reg64.rcx &&& st.regs.get64 Reg64.rcx) 0)
              (CfgLabel.label "LBB0_3")
          modifyIf (fun x => True)
              (setReg64 Reg64.rax fun st =>
                BitVec.setWidth 64 ((st.regs.get64 Reg64.rax).take 32 ^^^ (st.regs.get64 Reg64.rax).take 32))
          pure PUnit.unit),
        (CfgLabel.ofLabel
            { label := some "LBB0_2", idx := 1,
                body :=
                  [asm|
                      "mov r8, QWORD PTR [rsi+rax*8+0]"
                      "add r8, QWORD PTR [rdi+rax*8+0]"
                      "mov QWORD PTR [rdx+rax*8+0], r8"
                      "inc rax"
                      "cmp rcx, rax"
                      "jne LBB0_2"],
                next := some "LBB0_3" }.label,
          do
          modifyIf (loadOk 8 (sib 8 Reg64.rsi Reg64.rax 0))
              (loadReg 8 Reg64.r8 (sib 8 Reg64.rsi Reg64.rax 0) fun w x => w)
          modifyIf (loadOk 8 (sib 8 Reg64.rdi Reg64.rax 0))
              (loadReg 8 Reg64.r8 (sib 8 Reg64.rdi Reg64.rax 0) fun w st => w + st.regs.get64 Reg64.r8)
          modifyIf (storeOk 8 (sib 8 Reg64.rdx Reg64.rax 0))
              (storeWord 8 (sib 8 Reg64.rdx Reg64.rax 0) fun st => st.regs.get64 Reg64.r8)
          modifyIf (fun x => True) (setReg64 Reg64.rax fun st => st.regs.get64 Reg64.rax + 1)
          branch (fun st => CondCode.nz.cmp (st.regs.get64 Reg64.rcx) (st.regs.get64 Reg64.rax))
              (CfgLabel.label "LBB0_2")
          pure PUnit.unit),
        (CfgLabel.ofLabel
            { label := some "LBB0_3", idx := 2,
                body :=
                  [asm|
                      "ret"],
                next := none }.label,
          exitIf (loadOk 8 fun st => st.regs.get64 Reg64.rsp) (setReg64 Reg64.rsp fun st => st.regs.get64 Reg64.rsp + 8)
            CfgLabel.exit)]))
  CfgLabel.entry
-/
#guard_msgs in
#print zipWithAddA

/-! ## 3. A structured loop, by rewriting

`sym_simp_def` rewrites the block loop of `zipWithAddA` into an `if` and a `repeat'` loop over the
machine state: the jump of the loop block to itself becomes `continue`, and the return ends the
program in both branches. The command proves
the equation `zipWithAddT.eq`, so the first refinement carries over to `zipWithAddT`: -/

/--
info: @zipWithAddT.refines : ∀ [inst : Host] [inst_1 : FunDecls] [Embeds zipWithAdd] (s : MachineData) (ra : Int64),
  ⦃ fun x => x = s.push64 ra ⦄ zipWithAdd ⪯[ofStateRepr abs] zipWithAddT ⦃ fun x x_1 => ⊤; RetRel s ra ⦄
-/
#guard_msgs in
#check @zipWithAddT.refines

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

/-! ## 4. Registers as values, synthesized by `ascend_def`

The state is the data memory alone. The lifting relation, the one hint of the run, is
`RegsRel [(.rdi, rdi), …, (.rax, rax)]`: it names the registers that become values. `rdi`, `rsi`,
`rdx`, `rcx` and `rsp` are parameters, and `rax` is the value of the loop. The loaded values of
`r8` become variables. `ascend_def` synthesized `zipWithAddL₀`, and `sym_simp_def` states its
branch conditions as comparisons of the values in `zipWithAddL`. The return is an `assume` that the
return slot is mapped, followed by `throw CfgLabel.exit`: -/

/--
info: zipWithAddL.refines : ∀ (rdi rsi rdx rcx rsp : BitVec 64),
  ⦃ RegsRel [(Reg64.rdi, rdi), (Reg64.rsi, rsi), (Reg64.rdx, rdx), (Reg64.rcx, rcx), (Reg64.rsp, rsp)] ⦄
    zipWithAddT ⪯[ofStateRepr MachineData.dmem] (zipWithAddL rdi rsi rdx rcx rsp) ⦃ fun x x_1 x_2 => True;
    estack⟨fun l l' x => l = l'⟩ ⦄
-/
#guard_msgs in
#check @zipWithAddL.refines

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
      if ¬rcx = v + 1#64 then ⏎
        v := v + 1#64
      else
        assume fun m => (Mem.loadInt m rsp 8).isSome = true
        throw CfgLabel.exit
-/
#guard_msgs in
#print zipWithAddL

/-! ## 5. Arrays, synthesized by `ascend_def`

The state is the output array. The input arrays are parameters, named by their base addresses, and
the loads and the store become array reads and an array update. The words that count become
numbers: the loop counter `v` of `zipWithAddL` holds the number `i` (`v ≐ₙ i`), the length `rcx`
holds `n`, and the comparisons of the words become comparisons of the numbers. The relation of the
loop, the hint of the run, states `v ≐ₙ i`, the bound `i < n`, and the layout
`ArrayLayout 8 64 [(A, a), (B, b)] O n [rsp]` of the memory: the input arrays, the written array, and the
return slot. `ascend_def` synthesized `zipWithAddArr₀`, and `sym_simp_def` puts the array reads in
place and states the conditions as propositions in `zipWithAddArr`: -/

/--
info: zipWithAddArr.refines : ∀ (A B O rsp : BitVec 64) (n : Nat) (a b : Array (BitVec 64)),
  ⦃ fun m => A ≐ₐ a ∧ B ≐ₐ b ∧ a.size = n ∧ b.size = n ∧ ArrayLayout 8 64 [(A, a), (B, b)] O n [rsp] m ⦄
    (zipWithAddL A B O (BitVec.ofNat 64 n) rsp) ⪯[ofStateRepr (outView 8 64 O n)] (zipWithAddArr n a b) ⦃
    fun x x_1 x_2 => True; estack⟨fun l l' x => l = l'⟩ ⦄
-/
#guard_msgs in
#check @zipWithAddArr.refines

/--
info: def Ascent.Kraken.zipWithAddArr : Nat → Array (BitVec 64) → Array (BitVec 64) → BlockM (Array (BitVec 64)) Unit :=
fun n a b =>
  if n = 0 then throw CfgLabel.exit
  else do
    let mut i := 0
    repeat'
      modify fun o => o.set! i (a[i]! + b[i]!)
      if ¬n = i + 1 then ⏎
        i := i + 1
      else
        throw CfgLabel.exit
-/
#guard_msgs in
#print zipWithAddArr

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
                  words 8 64 t.dmem O n =
                    List.zipWith (fun x1 x2 => x1 + x2) (words 8 64 (s.push64 ra).dmem A n)
                      (words 8 64 (s.push64 ra).dmem B n) ⦄
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

/-! ## 9. A second program: `memmove`

The same chain refines clang's `memmove` of `n` bytes. The text copies backward when the destination
lies at or above the source, and forward otherwise. The register layer keeps both loops; the array
layer assumes that the source and the destination do not overlap, names the direction test `back`,
and reads the source as the array `a`: -/

/--
info: def Ascent.Kraken.memmoveArr : Nat → Array (BitVec 8) → Bool → BlockM (Array (BitVec 8)) Unit :=
fun n a back =>
  if back = true then
    if n = 0 then throw CfgLabel.exit
    else do
      let mut a_1 := (n, n)
      repeat'
        modify fun o => o.set! (a_1.snd - 1) a[a_1.snd - 1]!
        if ¬a_1.fst - 1 = 0 then
          a_1 := (a_1.fst - 1, a_1.fst - 1)
        else
          throw CfgLabel.exit
  else
    if n = 0 then throw CfgLabel.exit
    else do
      let mut a_1 := (0, n)
      repeat'
        modify fun o => o.set! a_1.fst a[a_1.fst]!
        if ¬a_1.snd = a_1.fst + 1 then
          a_1 := (a_1.fst + 1, a_1.snd)
        else
          throw CfgLabel.exit
-/
#guard_msgs in
#print memmoveArr

/-! `vcgen` proves that both loops leave the destination equal to `a`, and `ascend_def` synthesizes
the pure program from that result: -/

/--
info: def Ascent.Kraken.memmoveP : Array (BitVec 8) → Id (Array (BitVec 8)) :=
fun a => pure a
-/
#guard_msgs in
#print memmoveP

/-! The composition gives the result for the x64 text: -/

#check @memmove_correct
#print axioms memmove_correct

/-! ## 10. A third program: binary search

`bsearch` searches `n` signed words at `rdi` for `rdx` and returns an index or `-1`. Its loop runs
through several blocks, and `cfgLoop_header` makes the loop header `LBB0_3` a `repeat'`. A byte register
`r9b` tells the copies of the block `LBB0_2` whether to continue; moving each test before the register
writes that precede it gives the test the literal value of `r9b`, and the test folds away. The
registers become a loop over the bounds and the result register `rax`. An early return of the
machine code becomes a `break` that leaves the loop with `rax` set, and the function returns `rax`
after the loop: -/

/--
info: def Ascent.Kraken.bsearchL : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BlockM DataMem (BitVec 64) :=
fun rdi rsi rdx rax rsp => do
  let mut a := (0#64, rsi, rax)
  repeat'
    if a.snd.fst ≤ a.fst then
      assume fun m => (Mem.loadInt m rsp 8).isSome = true
      a := (a.fst, a.snd.fst, 18446744073709551615#64)
      break
    else
      let x ← load 8 (rdi + (a.fst + (a.snd.fst - a.fst).ushiftRight 1) * 8#64)
      if x.toInt < rdx.toInt then
        a := (a.fst + (a.snd.fst - a.fst).ushiftRight 1 + 1#64, a.snd.fst, a.snd.snd)
      else
        if x.toInt ≤ rdx.toInt then
          assume fun m => (Mem.loadInt m rsp 8).isSome = true
          a := (a.fst, a.snd.fst, a.fst + (a.snd.fst - a.fst).ushiftRight 1)
          break
        else
          a := (a.fst, a.fst + (a.snd.fst - a.fst).ushiftRight 1, a.snd.snd)
  pure a.snd.snd
-/
#guard_msgs in
#print bsearchL

/-! Over the array of words, the bounds are numbers `lo ≤ hi ≤ n`, and the result is an optional
index, `none` until the loop leaves: -/

/--
info: def Ascent.Kraken.bsearchArr : BitVec 64 → Nat → Array (BitVec 64) → BlockM Unit (Option Nat) :=
fun key n a => do
  let mut a_1 := (0, n, none)
  repeat'
    if a_1.snd.fst ≤ a_1.fst then
      a_1 := (a_1.fst, a_1.snd.fst, none)
      break
    else
      if a[a_1.fst + (a_1.snd.fst - a_1.fst) / 2]!.toInt < key.toInt then
        a_1 := (a_1.fst + (a_1.snd.fst - a_1.fst) / 2 + 1, a_1.snd.fst, a_1.snd.snd)
      else
        if a[a_1.fst + (a_1.snd.fst - a_1.fst) / 2]!.toInt ≤ key.toInt then
          a_1 := (a_1.fst, a_1.snd.fst, some (a_1.fst + (a_1.snd.fst - a_1.fst) / 2))
          break
        else
          a_1 := (a_1.fst, a_1.fst + (a_1.snd.fst - a_1.fst) / 2, a_1.snd.snd)
  pure a_1.snd.snd
-/
#guard_msgs in
#print bsearchArr

/-! `vcgen` proves that the loop returns the result of the recursive search `bsearchF`, and
`ascend_def` synthesizes the pure program: -/

/--
info: def Ascent.Kraken.bsearchP : BitVec 64 → Nat → Array (BitVec 64) → Id (Option Nat) :=
fun key n a => pure (bsearchF a key 0 n)
-/
#guard_msgs in
#print bsearchP

/-! `bsearchF` returns an index of `key`, or `none` when the sorted array does not hold `key`. The
composition gives the result for the x64 text: -/

#check @bsearch_correct
#print axioms bsearch_correct

end Ascent.Kraken.Walkthrough
