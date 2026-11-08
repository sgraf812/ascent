import Demo.ZipPure

/-!
# Binaries

A binary is a `ByteArray` of position-dependent machine code that the loader maps at the fixed
address `Binary.base`, the default text address of `ld` on x86-64. Execution starts at
`Binary.base` and is done when the program counter reaches `Binary.base + b.size`. A step reads
the bytes at the program counter, decodes them to one kraken `Instr` with `Binary.decode`, and runs
kraken's `Directives.interp` on it. The decoder covers exactly the encodings of `zipWithAdd`:

| bytes          | instruction            |
|----------------|------------------------|
| `48 85 /r`     | `test r/m64, r64`      |
| `7e ib`        | `jle rel8`             |
| `31 /r`        | `xor r/m32, r32`       |
| `4c 8b 04 SIB` | `mov r64, [b + i * s]` |
| `4c 03 04 SIB` | `add r64, [b + i * s]` |
| `4c 89 04 SIB` | `mov [b + i * s], r64` |
| `48 ff /0`     | `inc r/m64`            |
| `48 39 /r`     | `cmp r/m64, r64`       |
| `75 ib`        | `jne rel8`             |
| `c3`           | `ret`                  |

A jump decodes to its absolute target. The step interprets it under the label map that sends every
label to that target, so a binary has no labels of its own. A jump continues the run if its target
is the target of a direct jump in the binary (`Binary.targets`, a linear sweep over the bytes) and
the stack is at or below the stack of the call. Every other jump leaves the binary.

`Binary.wp` is the loop of kraken's `Program.wp` with this step, and it gives binaries their `WP`
instance. `Binary.Assembles p b` states that the host program is `p`, laid out from `Binary.base`
to `Binary.base + b.size`, that the bytes at every address of the host behave like the host's
directives there, and that the targets of the direct jumps of `b` are the labels of `p`.
`Binary.refines_program` turns it into `⦃P⦄ b ⪯[ofStateRepr id] p ⦃…⦄`.

`zipWithAddBinary` holds the 28 bytes that `llvm-mc` assembles from the text of `zipWithAdd`.
`zipWithAddHost_assembles` checks them against the host `zipWithAddHost`, which lays out
`zipWithAdd` from `Binary.base`.
-/

open Std.WP Lean.Order Ascent
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)
open scoped Program.WP

namespace Ascent.Kraken

namespace Binary

def base : Int64 := 0x401000

def fetch (b : ByteArray) (pc : Int64) : List UInt8 :=
  b.data.toList.drop (pc - base).toBitVec.toNat

/-! ## Decoding -/

def reg64 : Nat → Reg64
  | 0 => .rax | 1 => .rcx | 2 => .rdx | 3 => .rbx | 4 => .rsp | 5 => .rbp | 6 => .rsi | 7 => .rdi
  | 8 => .r8 | 9 => .r9 | 10 => .r10 | 11 => .r11 | 12 => .r12 | 13 => .r13 | 14 => .r14 | _ => .r15

def scale : Nat → Width
  | 0 => .W8 | 1 => .W16 | 2 => .W32 | _ => .W64

def fields (m : UInt8) : Nat × Nat × Nat :=
  (m.toNat / 64, m.toNat / 8 % 8, m.toNat % 8)

def regOf (x : Bool) (n : Nat) : Reg64 :=
  reg64 (if x then n + 8 else n)

def memOf (rexX rexB : Bool) (sib : UInt8) : AddrExpr :=
  let (s, i, bs) := fields sib
  { base := some (.reg (regOf rexB bs)), idx := some { reg := regOf rexX i, scale := scale s } }

def decodeW (r x b' : Bool) : List UInt8 → Option (Instr × Nat)
  | 0x85 :: m :: _ =>
    let (md, rg, rm) := fields m
    if md = 3 then
      some (.regular .W64 .W64
        (.test (.reg (.low (regOf b' rm) .W64)) (.regOrMem (.reg (.low (regOf r rg) .W64)))), 2)
    else none
  | 0x39 :: m :: _ =>
    let (md, rg, rm) := fields m
    if md = 3 then
      some (.regular .W64 .W64
        (.cmp (.reg (.low (regOf b' rm) .W64)) (.regOrMem (.reg (.low (regOf r rg) .W64)))), 2)
    else none
  | 0xff :: m :: _ =>
    let (md, rg, rm) := fields m
    if md = 3 ∧ rg = 0 then some (.regular .W64 .W64 (.inc (.reg (.low (regOf b' rm) .W64))), 2)
    else none
  | 0x8b :: m :: sib :: _ =>
    let (md, rg, rm) := fields m
    if md = 0 ∧ rm = 4 then
      some (.regular .W64 .W64
        (.mov (.reg (.low (regOf r rg) .W64)) (.regOrMem (.mem (memOf x b' sib)))), 3)
    else none
  | 0x03 :: m :: sib :: _ =>
    let (md, rg, rm) := fields m
    if md = 0 ∧ rm = 4 then
      some (.regular .W64 .W64
        (.add (.reg (.low (regOf r rg) .W64)) (.regOrMem (.mem (memOf x b' sib)))), 3)
    else none
  | 0x89 :: m :: sib :: _ =>
    let (md, rg, rm) := fields m
    if md = 0 ∧ rm = 4 then
      some (.regular .W64 .W64
        (.mov (.mem (memOf x b' sib)) (.regOrMem (.reg (.low (regOf r rg) .W64)))), 3)
    else none
  | _ => none

def decodeJcc (pc : Int64) (cc : CondCode) (d : UInt8) : Option (Instr × Nat × Option Int64) :=
  some (.regular .W64 .W64 (.jcc cc ""), 2, some (pc + 2 + Int64.ofInt d.toBitVec.toInt))

def decode (pc : Int64) : List UInt8 → Option (Instr × Nat × Option Int64)
  | 0xc3 :: _ => some (.regular .W64 .W64 .ret, 1, none)
  | 0x7e :: d :: _ => decodeJcc pc .le d
  | 0x75 :: d :: _ => decodeJcc pc .nz d
  | 0x31 :: m :: _ =>
    let (md, rg, rm) := fields m
    if md = 3 then
      some (.regular .W64 .W32
        (.xor (.reg (.low (reg64 rm) .W32)) (.regOrMem (.reg (.low (reg64 rg) .W32)))), 2, none)
    else none
  | rex :: rest =>
    if rex.toNat / 16 = 4 ∧ rex.toNat / 8 % 2 = 1 then
      (decodeW (rex.toNat / 4 % 2 = 1) (rex.toNat / 2 % 2 = 1) (rex.toNat % 2 = 1) rest).map
        fun (i, n) => (i, n + 1, none)
    else none
  | [] => none

def decodeAt (b : ByteArray) (pc : Int64) : Option (Instr × Nat × Option Int64) :=
  decode pc (fetch b pc)

def directivesAt (b : ByteArray) (pc : Int64) : List (Kraken.Sized Directive) :=
  match decodeAt b pc with
  | some (i, n, _) => [⟨.instr i, n⟩]
  | none => []

@[instance_reducible] def labelsAt (b : ByteArray) (pc : Int64) : Labels :=
  ⟨fun _ => ((decodeAt b pc).bind (·.2.2)).getD 0⟩

def targetsFrom (b : ByteArray) : Nat → Int64 → List Int64
  | 0, _ => []
  | fuel + 1, pc =>
    match decodeAt b pc with
    | some (_, n, t) => t.toList ++ targetsFrom b fuel (pc + .ofNat n)
    | none => []

def targets (b : ByteArray) : List Int64 :=
  targetsFrom b b.size base

/-! ## The loop -/

def StepIn (b : ByteArray) (next jump : MachineState → Prop) (st : MachineState) : Prop :=
  let := labelsAt b st.pc
  ∀ ⦃P : MachineState → Prop⦄ ⦃ret jmp : MachineState → Effects⦄,
    (∀ st', next st' → (ret st').All P) → (∀ st', jump st' → (jmp st').All P) →
      (Directives.interp (directivesAt b st.pc) st.data st.pc (fun a s => ret ⟨s, a⟩)
        (fun a s => jmp ⟨s, a⟩)).All P

theorem StepIn.mono {b : ByteArray} {next₁ next₂ jump₁ jump₂ : MachineState → Prop} {st : MachineState}
    (h : StepIn b next₁ jump₁ st) (hn : ∀ u, next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u) :
    StepIn b next₂ jump₂ st :=
  fun _ _ _ hr hk => h (fun u h => hr u (hn u h)) (fun u h => hk u (hj u h))

open Classical in
def ContinueOnInternalExit (b : ByteArray) (s : MachineData) («continue» exit : MachineState → Prop)
    (st : MachineState) : Prop :=
  if st.pc ∈ targets b ∧ st.data.StackAtOrBelow s then «continue» st else exit st

def wp (b : ByteArray) (done exit : MachineState → Prop) (s : MachineData) : Prop :=
  While (·.pc ≠ base + .ofNat b.size)
    (fun «continue» => StepIn b «continue» (ContinueOnInternalExit b s «continue» exit)) done ⟨s, base⟩

theorem wp_mono {b : ByteArray} {done₁ done₂ exit₁ exit₂ : MachineState → Prop}
    (hd : ∀ u, done₁ u → done₂ u) (he : ∀ u, exit₁ u → exit₂ u) {s : MachineData}
    (h : wp b done₁ exit₁ s) : wp b done₂ exit₂ s :=
  While.imp (fun _ _ _ hb => hb.mono (fun _ h => h) fun u h => by
      unfold ContinueOnInternalExit at h ⊢
      split at h
      · rw [ite_eq_left ‹_›]; exact h
      · rw [ite_eq_right ‹_›]; exact he _ h)
    (fun _ _ h => hd _ h) h

end Binary

instance : WP ByteArray Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans b := ⟨fun Q E s => Binary.wp b (fun st => Q () st.data) (fun st => E st.pc st.data) s⟩
  trans_monotone _ := fun _ _ _ _ hE hQ _ h =>
    Binary.wp_mono (fun st => hQ () st.data) (fun st => hE st.pc st.data) h

namespace Binary

theorem wp_eq (b : ByteArray) (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (s : MachineData) : Std.WP.wp b Q E s = wp b (fun st => Q () st.data) (fun st => E st.pc st.data) s :=
  rfl

/-! ## Binaries refine programs -/

theorem label_inert (l : Label) : (Directive.label l).Inert := fun _ _ _ _ _ => Iff.rfl

theorem interp_jcc (L L' : Labels) {l l' : Label} (h : L.label l = L'.label l') (asz osz : Width)
    (cc : CondCode) (n : Nat) (s : MachineData) (pc : Int64) (ret jmp : Int64 → MachineData → Effects) :
    @Directives.interp L [⟨.instr (.regular asz osz (.jcc cc l)), n⟩] s pc ret jmp
      = @Directives.interp L' [⟨.instr (.regular asz osz (.jcc cc l')), n⟩] s pc ret jmp := by
  simp only [Directives.interp, Directive.interp, Instr.interp, Operation.interp]
  rw [h]

section
variable [Host]

structure Assembles (p : Program) (b : ByteArray) : Prop where
  prog : Host.prog = p
  start : Host.addrOf 0 = base
  stop : Host.addrOf p.length = base + .ofNat b.size
  decodes : ∀ a, Host.exe.directivesAtAddress a ≠ [] → ∀ s ret jmp,
    @Directives.interp Host.exe.labels (Host.exe.directivesAtAddress a) s a ret jmp
      = @Directives.interp (labelsAt b a) (directivesAt b a) s a ret jmp
  targets : ∀ a, a ∈ targets b ↔ p.InternalTarget a

@[instance_reducible] def Assembles.embeds {p : Program} {b : ByteArray} (h : Assembles p b) : Embeds p :=
  ⟨⟨0, h.prog ▸ List.prefix_refl _⟩⟩

theorem stepIn_of_exe {b : ByteArray} {next jump : MachineState → Prop} {st : MachineState}
    (hdec : ∀ s ret jmp, @Directives.interp Host.exe.labels (Host.exe.directivesAtAddress st.pc) s st.pc ret jmp
      = @Directives.interp (labelsAt b st.pc) (directivesAt b st.pc) s st.pc ret jmp)
    (h : Host.exe.StepIn next jump st) : StepIn b next jump st := by
  intro P ret jmp hr hj
  have h' := h hr hj
  show (@Directives.interp (labelsAt b st.pc) _ _ _ _ _).All P
  rw [← hdec]
  exact h'

theorem stutter_of_exe {next jump : MachineState → Prop} {st : MachineState}
    (hnil : Host.exe.directivesAtAddress st.pc = []) (h : Host.exe.StepIn next jump st) : next st := by
  have hne : (⟨st.data, st.pc + 1⟩ : MachineState) ≠ st := fun he => by
    have := congrArg MachineState.pc he
    simp at this
  have h' := @h (fun u => u = st → next u) (fun u => .done u) (fun _ => .done ⟨st.data, st.pc + 1⟩)
    (fun _ hu _ => hu) (fun _ _ he => absurd he hne)
  rw [hnil] at h'
  exact h' rfl

theorem wp_of_program_wp {b : ByteArray} {p : Program} (h : Assembles p b)
    {done exit : MachineState → Prop} {s : MachineData} (hw : p.wp done exit s) : wp b done exit s := by
  let _ : Embeds p := h.embeds
  have hcont : ∀ c u, p.ContinueOnInternalExit s c exit u = ContinueOnInternalExit b s c exit u := by
    intro c u
    unfold Program.ContinueOnInternalExit ContinueOnInternalExit
    by_cases hc : p.InternalTarget u.pc ∧ u.data.StackAtOrBelow s
    · rw [ite_eq_left hc, ite_eq_left ⟨(h.targets _).2 hc.1, hc.2⟩]
    · rw [ite_eq_right hc, ite_eq_right fun hb => hc ⟨(h.targets _).1 hb.1, hb.2⟩]
  rw [Program.wp_eq] at hw
  have hw := @hw h.embeds
  unfold wp
  have hstart : h.embeds.embedding.startAddr = base := h.start
  have hstop : h.embeds.embedding.endAddr = base + .ofNat b.size := by
    show Host.addrOf (0 + p.length) = _
    simpa using h.stop
  rw [hstart, hstop] at hw
  unfold While at hw ⊢
  generalize (⟨s, base⟩ : MachineState) = x₀ at hw ⊢
  induction hw with
  | done x hx => exact .done x hx
  | step x mid hx _ ih =>
    obtain ⟨hc, hstep⟩ := hx
    by_cases hnil : Host.exe.directivesAtAddress x.pc = []
    · exact ih x (stutter_of_exe hnil hstep)
    · refine .step x mid ⟨hc, ?_⟩ ih
      exact (stepIn_of_exe (h.decodes x.pc hnil) hstep).mono (fun _ h => h)
        fun u h => by rw [← hcont]; exact h

theorem refines_program {b : ByteArray} {p : Program} (h : Assembles p b) (P : MachineData → Prop) :
    ⦃P⦄ b ⪯[ofStateRepr id] p ⦃fun _ _ _ => True; fun a a' _ => a = a'⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, id] at hs
  refine wp_mono (fun u hu => ?_) (fun u hu => ?_) (wp_of_program_wp h hs.2)
  · show (ofStateRepr id).post _ Qa () u.data
    rw [Concretization.post_pi]
    exact ⟨(), trivial, hu⟩
  · show (ofStateRepr id).post _ Ea u.pc u.data
    rw [Concretization.post_pi]
    exact ⟨u.pc, rfl, hu⟩

end

end Binary

end Ascent.Kraken

namespace Ascent.Kraken

/-! ## `zipWithAdd` as bytes -/

@[instance_reducible] def zipWithAddLayout : Layout where
  start := 0x401000
  size i := ([3, 2, 2, 0, 4, 4, 4, 3, 3, 2, 0, 1] : List Nat)[i]?.getD 0

theorem zipWithAddLayout_size (i : Nat) : @Kraken.Layout.size Directive zipWithAddLayout i =
    ([3, 2, 2, 0, 4, 4, 4, 3, 3, 2, 0, 1] : List Nat)[i]?.getD 0 := rfl

theorem zipWithAddLayout_start : @Kraken.Layout.start Directive zipWithAddLayout = 0x401000 := rfl

def zipWithAddBinary : ByteArray :=
  ⟨#[0x48, 0x85, 0xc9, 0x7e, 0x16, 0x31, 0xc0, 0x4c, 0x8b, 0x04, 0xc6, 0x4c, 0x03, 0x04, 0xc7,
    0x4c, 0x89, 0x04, 0xc2, 0x48, 0xff, 0xc0, 0x48, 0x39, 0xc1, 0x75, 0xec, 0xc3]⟩

theorem _root_.Kraken.Executable.exists_addr_of_directivesAtAddress_ne_nil {e : Executable} {a : Int64}
    (h : e.directivesAtAddress a ≠ []) : ∃ x ∈ e.withAddresses, x.addr = a := by
  unfold Kraken.Executable.directivesAtAddress at h
  generalize e.withAddresses = l at h ⊢
  induction l with
  | nil => simp at h
  | cons x l ih =>
    by_cases hx : x.addr = a
    · exact ⟨x, List.mem_cons_self, hx⟩
    · simp only [List.dropWhile_cons, hx, ne_eq, not_false_eq_true, decide_true] at h
      obtain ⟨y, hy, rfl⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, rfl⟩

theorem zipWithAddLayout_sizeBefore (n : Nat) :
    (zipWithAddLayout.apply zipWithAdd).sizeBefore n = (([3, 2, 2, 0, 4, 4, 4, 3, 3, 2, 0, 1] : List Nat).take n).sum := by
  rcases n with _|_|_|_|_|_|_|_|_|_|_|_|n <;>
    simp [Kraken.Executable.sizeBefore, Kraken.Layout.apply, zipWithAdd, zipWithAddLayout_size]

theorem zipWithAddLayout_sizeBefore_le (n : Nat) : (zipWithAddLayout.apply zipWithAdd).sizeBefore n ≤ 28 := by
  rw [zipWithAddLayout_sizeBefore]
  rcases n with _|_|_|_|_|_|_|_|_|_|_|_|n <;> simp

theorem zipWithAddLayout_startAddr : (zipWithAddLayout.apply zipWithAdd).startAddr = 0x401000 := rfl

theorem zipWithAddLayout_addrOf_sub (n : Nat) :
    ((zipWithAddLayout.apply zipWithAdd).addrOf n - 0x401000).toBitVec.toNat =
      (zipWithAddLayout.apply zipWithAdd).sizeBefore n := by
  have hb := zipWithAddLayout_sizeBefore_le n
  simp [Kraken.Executable.addrOf, zipWithAddLayout_startAddr]
  omega

@[instance_reducible] def zipWithAddHost : Host where
  prog := zipWithAdd
  layout := zipWithAddLayout
  labels_nodup := by simp [zipWithAdd]
  label_size i l h := by
    rcases i with _|_|_|_|_|_|_|_|_|_|_|_|i <;> simp_all [zipWithAdd, zipWithAddLayout_size]
  instr_size_pos i ins h _ := by
    rcases i with _|_|_|_|_|_|_|_|_|_|_|_|i <;> simp_all [zipWithAdd, zipWithAddLayout_size]
  instr_addr_ne i _ _ h := by
    have hb := zipWithAddLayout_sizeBefore_le i
    have h' := zipWithAddLayout_addrOf_sub i
    rw [h] at h'
    simp at h'
    omega
  zero_inert i d h hz := by
    rcases i with _|_|_|_|_|_|_|_|_|_|_|_|i <;> simp [zipWithAdd, zipWithAddLayout_size] at h hz <;>
      (subst h; exact Binary.label_inert _)
  addr_determines_offset j k h := by
    rw [← zipWithAddLayout_addrOf_sub, ← zipWithAddLayout_addrOf_sub, h]

section
attribute [local instance] zipWithAddHost

theorem zipWithAddHost_exe : Host.exe = zipWithAddLayout.apply zipWithAdd := rfl

theorem zipWithAddHost_label (l : Label) : Host.exe.labels.label l =
    if l = "LBB0_2" then 0x401007 else if l = "LBB0_3" then 0x40101b else -1 := by
  rw [zipWithAddHost_exe]
  show ((zipWithAddLayout.apply zipWithAdd).withAddresses.findSome? _).getD (-1) = _
  by_cases h₁ : l = "LBB0_2"
  · subst h₁
    simp [Kraken.Layout.apply, zipWithAdd, Kraken.Executable.withAddresses, zipWithAddLayout_size,
      zipWithAddLayout_start]
  by_cases h₂ : l = "LBB0_3"
  · subst h₂
    simp [Kraken.Layout.apply, zipWithAdd, Kraken.Executable.withAddresses, zipWithAddLayout_size,
      zipWithAddLayout_start]
  simp [Kraken.Layout.apply, zipWithAdd, Kraken.Executable.withAddresses, zipWithAddLayout_size,
    zipWithAddLayout_start, h₁, h₂, Ne.symm h₁, Ne.symm h₂]

theorem zipWithAddBinary_targets : Binary.targets zipWithAddBinary = [0x40101b, 0x401007] := rfl

theorem zipWithAddHost_assembles : Binary.Assembles zipWithAdd zipWithAddBinary where
  prog := rfl
  start := rfl
  stop := by
    show Host.addrOf 12 = _
    rw [Host.addrOf, zipWithAddHost_exe, Kraken.Executable.addrOf, zipWithAddLayout_sizeBefore,
      zipWithAddLayout_startAddr]
    rfl
  decodes a hne s ret jmp := by
    obtain ⟨x, hx, rfl⟩ := Kraken.Executable.exists_addr_of_directivesAtAddress_ne_nil hne
    rw [zipWithAddHost_exe] at hx ⊢
    simp [Kraken.Layout.apply, zipWithAdd, Kraken.Executable.withAddresses, zipWithAddLayout_size,
      zipWithAddLayout_start] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp [Kraken.Layout.apply, zipWithAdd, Kraken.Executable.withAddresses,
        Kraken.Executable.directivesAtAddress, zipWithAddLayout_size, zipWithAddLayout_start]
      first
        | rfl
        | refine (Binary.interp_jcc _ _ (l' := "") ?_ _ _ _ _ _ _ _ _).trans rfl
          exact (zipWithAddHost_label _).trans (by simp <;> rfl)
  targets a := by
    rw [zipWithAddBinary_targets]
    simp only [Program.InternalTarget, zipWithAddHost_label]
    simp [zipWithAdd]
    exact or_comm.trans (or_congr eq_comm eq_comm)

end

section
variable [Host] (s : MachineData) (ra : Int64)

theorem zipWithAddBinary_refines_zipWithAdd (h : Binary.Assembles zipWithAdd zipWithAddBinary)
    (P : MachineData → Prop) :
    ⦃P⦄ zipWithAddBinary ⪯[ofStateRepr id] zipWithAdd ⦃fun _ _ _ => True; fun a a' _ => a = a'⦄ :=
  Binary.refines_program h P

theorem zipWithAddBinary_refines_P (h : Binary.Assembles zipWithAdd zipWithAddBinary) {A B O : BitVec 64}
    {n : Nat} (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    ⦃(· = s.push64 ra)⦄ zipWithAddBinary
      ⪯[(ofStateRepr id).comp (machineToArray O n)]
      (zipWithAddP (words (s.push64 ra).dmem A n).toArray (words (s.push64 ra).dmem B n).toArray)
      ⦃fun _ _ _ => False; fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        outView O n t.dmem = Id.run (zipWithAddP (words (s.push64 ra).dmem A n).toArray
          (words (s.push64 ra).dmem B n).toArray)⦄ :=
  let _ : Embeds zipWithAdd := h.embeds
  Refinement.comp_le (by grind) (by grind) (by grind)
    (zipWithAdd_refines_P s ra hrdi hrsi hrdx hrcx hmem) (zipWithAddBinary_refines_zipWithAdd h _)

theorem zipWithAddBinary_correct (hasm : Binary.Assembles zipWithAdd zipWithAddBinary) {A B O : BitVec 64}
    {n : Nat} (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    Triple zipWithAddBinary (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
        ∧ words t.dmem O n = List.zipWith (· + ·) (words (s.push64 ra).dmem A n)
            (words (s.push64 ra).dmem B n)) := by
  let _ : Embeds zipWithAdd := hasm.embeds
  have h := (zipWithAddBinary_refines_P s ra hasm hrdi hrsi hrdx hrcx hmem).transport
    (Pa := True) (Qa := fun _ => True) (Ea := estack⟨⟩) ⟨fun _ => trivial⟩
  refine ⟨fun t ht => WP.wp_monotone (x := zipWithAddBinary) (fun _ _ _ => trivial) ?_ t
    (h.le_wp t (by simp only [meet_apply, meet_prop_eq_and, Concretization.comp_pred,
      ofStateRepr_pred, purify_pred]; exact ⟨ht, trivial⟩))⟩
  rintro a t ⟨hra, hrsp, ho⟩
  exact ⟨hra, hrsp, words_eq_zipWith_of_outView ho⟩

end

theorem zipWithAddHost_correct (s : MachineData) (ra : Int64) {A B O : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    Triple zipWithAddBinary (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
        ∧ words t.dmem O n = List.zipWith (· + ·) (words (s.push64 ra).dmem A n)
            (words (s.push64 ra).dmem B n)) :=
  @zipWithAddBinary_correct zipWithAddHost s ra zipWithAddHost_assembles A B O n hrdi hrsi hrdx hrcx hmem

end Ascent.Kraken
