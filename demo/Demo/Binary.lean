import Demo.ZipPure

/-!
# Binaries

A `Binary` is a text segment `text` mapped at `base`, its symbol table `symbols`, the address
`entry` where it starts and the address `stop` where it ends. A step reads the bytes at the program
counter, decodes them to one kraken `Instr` with `Binary.decode`, and runs kraken's
`Directives.interp` on it. The decoder covers exactly the encodings of `zipWithAdd`:

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

A jump decodes to the symbol at its target, and the labels of a binary are its symbols.

`Binary.wp` is the loop of kraken's `Program.wp` with this step in place of the step of the host
program, and it gives binaries their `WP` instance. `Binary.DecodesTo b` states that at every
address where the host program has directives, they are size-zero inert directives followed by the
instruction that `b` decodes there. `Binary.refines_program` turns this into
`⦃P⦄ b ⪯[ofStateRepr id] p ⦃…⦄`.

`zipWithAddBinary` holds the 28 bytes that `llvm-mc` assembles from the text of `zipWithAdd`, mapped
at `0x401000`. The host `zipWithAddHost` places `zipWithAdd` at the same address, and
`zipWithAddBinary_decodesTo` checks the decoder against the layout address by address.
-/

open Std.WP Lean.Order Ascent
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)
open scoped Program.WP

namespace Ascent.Kraken

structure Binary where
  base : Int64
  text : List UInt8
  symbols : List (Label × Int64)
  entry : Int64
  stop : Int64

namespace Binary

def fetch (b : Binary) (pc : Int64) : List UInt8 :=
  b.text.drop (pc - b.base).toBitVec.toNat

@[instance_reducible] def labels (b : Binary) : Labels :=
  ⟨fun l => ((b.symbols.find? (·.1 == l)).map (·.2)).getD (-1)⟩

def symbolAt (b : Binary) (a : Int64) : Option Label :=
  (b.symbols.find? (·.2 == a)).map (·.1)

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

def decodeJcc (b : Binary) (pc : Int64) (cc : CondCode) (d : UInt8) : Option (Instr × Nat) :=
  (b.symbolAt (pc + 2 + Int64.ofInt d.toBitVec.toInt)).map fun l => (.regular .W64 .W64 (.jcc cc l), 2)

def decode (b : Binary) (pc : Int64) : List UInt8 → Option (Instr × Nat)
  | 0xc3 :: _ => some (.regular .W64 .W64 .ret, 1)
  | 0x7e :: d :: _ => b.decodeJcc pc .le d
  | 0x75 :: d :: _ => b.decodeJcc pc .nz d
  | 0x31 :: m :: _ =>
    let (md, rg, rm) := fields m
    if md = 3 then
      some (.regular .W64 .W32
        (.xor (.reg (.low (reg64 rm) .W32)) (.regOrMem (.reg (.low (reg64 rg) .W32)))), 2)
    else none
  | rex :: rest =>
    if rex.toNat / 16 = 4 ∧ rex.toNat / 8 % 2 = 1 then
      (decodeW (rex.toNat / 4 % 2 = 1) (rex.toNat / 2 % 2 = 1) (rex.toNat % 2 = 1) rest).map
        fun (i, n) => (i, n + 1)
    else none
  | [] => none

def directivesAt (b : Binary) (pc : Int64) : List (Kraken.Sized Directive) :=
  match b.decode pc (b.fetch pc) with
  | some (i, n) => [⟨.instr i, n⟩]
  | none => []

/-! ## The loop -/

def StepIn (b : Binary) (next jump : MachineState → Prop) (st : MachineState) : Prop :=
  let := b.labels
  ∀ ⦃P : MachineState → Prop⦄ ⦃ret jmp : MachineState → Effects⦄,
    (∀ st', next st' → (ret st').All P) → (∀ st', jump st' → (jmp st').All P) →
      (Directives.interp (b.directivesAt st.pc) st.data st.pc (fun a s => ret ⟨s, a⟩)
        (fun a s => jmp ⟨s, a⟩)).All P

theorem StepIn.mono {b : Binary} {next₁ next₂ jump₁ jump₂ : MachineState → Prop} {st : MachineState}
    (h : b.StepIn next₁ jump₁ st) (hn : ∀ u, next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u) :
    b.StepIn next₂ jump₂ st :=
  fun _ _ _ hr hk => h (fun u h => hr u (hn u h)) (fun u h => hk u (hj u h))

def InternalTarget (b : Binary) (a : Int64) : Prop :=
  ∃ l ∈ b.symbols.map Prod.fst, b.labels.label l = a

open Classical in
def ContinueOnInternalExit (b : Binary) (s : MachineData) («continue» exit : MachineState → Prop)
    (st : MachineState) : Prop :=
  if b.InternalTarget st.pc ∧ st.data.StackAtOrBelow s then «continue» st else exit st

def wp (b : Binary) (done exit : MachineState → Prop) (s : MachineData) : Prop :=
  While (·.pc ≠ b.stop) (fun «continue» => b.StepIn «continue» (b.ContinueOnInternalExit s «continue» exit))
    done ⟨s, b.entry⟩

theorem wp_mono {b : Binary} {done₁ done₂ exit₁ exit₂ : MachineState → Prop}
    (hd : ∀ u, done₁ u → done₂ u) (he : ∀ u, exit₁ u → exit₂ u) {s : MachineData}
    (h : b.wp done₁ exit₁ s) : b.wp done₂ exit₂ s :=
  While.imp (fun _ _ _ hb => hb.mono (fun _ h => h) fun u h => by
      unfold ContinueOnInternalExit at h ⊢
      split at h
      · rw [ite_eq_left ‹_›]; exact h
      · rw [ite_eq_right ‹_›]; exact he _ h)
    (fun _ _ h => hd _ h) h

instance : WP Binary Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans b := ⟨fun Q E s => b.wp (fun st => Q () st.data) (fun st => E st.pc st.data) s⟩
  trans_monotone _ := fun _ _ _ _ hE hQ _ h => wp_mono (fun st => hQ () st.data) (fun st => hE st.pc st.data) h

theorem wp_eq (b : Binary) (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop) (s : MachineData) :
    Std.WP.wp b Q E s = b.wp (fun st => Q () st.data) (fun st => E st.pc st.data) s := rfl

/-! ## Binaries refine programs -/

theorem label_inert (l : Label) : (Directive.label l).Inert := fun _ _ _ _ _ => Iff.rfl

section
variable [Host]

def DecodesTo (b : Binary) : Prop :=
  ∀ a, Host.exe.directivesAtAddress a ≠ [] → ∃ pre, (∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert) ∧
    Host.exe.directivesAtAddress a = pre ++ b.directivesAt a

theorem stepIn_of_exe {b : Binary} {next jump : MachineState → Prop} {st : MachineState}
    {pre : List (Kraken.Sized Directive)} (hpre : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert)
    (hlab : b.labels = Host.exe.labels)
    (hat : Host.exe.directivesAtAddress st.pc = pre ++ b.directivesAt st.pc)
    (h : Host.exe.StepIn next jump st) : b.StepIn next jump st := by
  intro P ret jmp hr hj
  have h' := h hr hj
  rw [hat] at h'
  have h'' := (@Directives.interp_inert_append Host.exe.labels pre (b.directivesAt st.pc) hpre
    st.data st.pc (fun a s => ret ⟨s, a⟩) P (fun a s => jmp ⟨s, a⟩)).mp h'
  show (@Directives.interp b.labels _ _ _ _ _).All P
  rw [hlab]
  exact h''

theorem stutter_of_exe {next jump : MachineState → Prop} {st : MachineState}
    (hnil : Host.exe.directivesAtAddress st.pc = []) (h : Host.exe.StepIn next jump st) : next st := by
  have hne : (⟨st.data, st.pc + 1⟩ : MachineState) ≠ st := fun he => by
    have := congrArg MachineState.pc he
    simp at this
  have h' := @h (fun u => u = st → next u) (fun u => .done u) (fun _ => .done ⟨st.data, st.pc + 1⟩)
    (fun _ hu _ => hu) (fun _ _ he => absurd he hne)
  rw [hnil] at h'
  exact h' rfl

theorem wp_of_program_wp {b : Binary} {p : Program} [h : Embeds p]
    (hdec : b.DecodesTo) (hlab : b.labels = Host.exe.labels) (hsym : b.symbols.map Prod.fst = p.labels)
    (hentry : b.entry = h.embedding.startAddr) (hstop : b.stop = h.embedding.endAddr)
    {done exit : MachineState → Prop} {s : MachineData} (hw : p.wp done exit s) : b.wp done exit s := by
  have hcont : ∀ c u, p.ContinueOnInternalExit s c exit u = b.ContinueOnInternalExit s c exit u := by
    intro c u
    have ht : p.InternalTarget u.pc = b.InternalTarget u.pc := by
      unfold Program.InternalTarget InternalTarget
      rw [hsym, hlab]
    unfold Program.ContinueOnInternalExit ContinueOnInternalExit
    rw [ht]
  rw [Program.wp_eq] at hw
  have hw := @hw h
  unfold wp
  rw [hentry, hstop]
  unfold While at hw ⊢
  generalize (⟨s, h.embedding.startAddr⟩ : MachineState) = x₀ at hw ⊢
  induction hw with
  | done x hx => exact .done x hx
  | step x mid hx _ ih =>
    obtain ⟨hc, hstep⟩ := hx
    by_cases hnil : Host.exe.directivesAtAddress x.pc = []
    · exact ih x (stutter_of_exe hnil hstep)
    · obtain ⟨pre, hpre, hat⟩ := hdec x.pc hnil
      refine .step x mid ⟨hc, ?_⟩ ih
      exact (stepIn_of_exe hpre hlab hat hstep).mono (fun _ h => h) fun u h => by rw [← hcont]; exact h

theorem refines_program {b : Binary} {p : Program} [h : Embeds p]
    (hdec : b.DecodesTo) (hlab : b.labels = Host.exe.labels) (hsym : b.symbols.map Prod.fst = p.labels)
    (hentry : b.entry = h.embedding.startAddr) (hstop : b.stop = h.embedding.endAddr) (P : MachineData → Prop) :
    ⦃P⦄ b ⪯[ofStateRepr id] p ⦃fun _ _ _ => True; fun a a' _ => a = a'⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, id] at hs
  refine wp_mono (fun u hu => ?_) (fun u hu => ?_) (wp_of_program_wp hdec hlab hsym hentry hstop hs.2)
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

def zipWithAddBinary : Binary where
  base := 0x401000
  text := [0x48, 0x85, 0xc9, 0x7e, 0x16, 0x31, 0xc0, 0x4c, 0x8b, 0x04, 0xc6, 0x4c, 0x03, 0x04, 0xc7,
    0x4c, 0x89, 0x04, 0xc2, 0x48, 0xff, 0xc0, 0x48, 0x39, 0xc1, 0x75, 0xec, 0xc3]
  symbols := [("LBB0_2", 0x401007), ("LBB0_3", 0x40101b)]
  entry := 0x401000
  stop := 0x40101c

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

local instance : Embeds zipWithAdd := ⟨⟨0, List.prefix_refl _⟩⟩

theorem zipWithAddHost_exe : Host.exe = zipWithAddLayout.apply zipWithAdd := rfl

theorem zipWithAddBinary_labels : zipWithAddBinary.labels = Host.exe.labels := by
  rw [zipWithAddHost_exe]
  unfold Binary.labels Executable.labels
  congr 1
  funext l
  by_cases h₁ : "LBB0_2" = l <;> by_cases h₂ : "LBB0_3" = l <;>
    simp_all [zipWithAddBinary, Kraken.Layout.apply, zipWithAdd, Kraken.Executable.withAddresses,
      zipWithAddLayout_size, zipWithAddLayout_start, beq_iff_eq]

theorem zipWithAddBinary_symbols : zipWithAddBinary.symbols.map Prod.fst = zipWithAdd.labels := by
  simp [zipWithAddBinary, zipWithAdd]

theorem zipWithAddBinary_entry :
    zipWithAddBinary.entry = (inferInstance : Embeds zipWithAdd).embedding.startAddr := rfl

theorem zipWithAddBinary_stop :
    zipWithAddBinary.stop = (inferInstance : Embeds zipWithAdd).embedding.endAddr := by
  show (0x40101c : Int64) = Host.addrOf (0 + zipWithAdd.length)
  rw [show zipWithAdd.length = 12 from rfl, Host.addrOf, zipWithAddHost_exe, Kraken.Executable.addrOf,
    zipWithAddLayout_sizeBefore, zipWithAddLayout_startAddr]
  rfl

theorem zipWithAddBinary_decodesTo : zipWithAddBinary.DecodesTo := by
  intro a hne
  obtain ⟨x, hx, rfl⟩ := Kraken.Executable.exists_addr_of_directivesAtAddress_ne_nil hne
  rw [zipWithAddHost_exe] at hx ⊢
  simp [Kraken.Layout.apply, zipWithAdd, Kraken.Executable.withAddresses, zipWithAddLayout_size,
    zipWithAddLayout_start] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | exact ⟨[], by simp, by
        simp [Kraken.Layout.apply, zipWithAdd, Kraken.Executable.withAddresses,
          Kraken.Executable.directivesAtAddress, zipWithAddLayout_size, zipWithAddLayout_start]
        rfl⟩
    | exact ⟨[⟨.label "LBB0_2", 0⟩], by simp [Binary.label_inert], by
        simp [Kraken.Layout.apply, zipWithAdd, Kraken.Executable.withAddresses,
          Kraken.Executable.directivesAtAddress, zipWithAddLayout_size, zipWithAddLayout_start]
        rfl⟩
    | exact ⟨[⟨.label "LBB0_3", 0⟩], by simp [Binary.label_inert], by
        simp [Kraken.Layout.apply, zipWithAdd, Kraken.Executable.withAddresses,
          Kraken.Executable.directivesAtAddress, zipWithAddLayout_size, zipWithAddLayout_start]
        rfl⟩

theorem zipWithAddBinary_refines_zipWithAdd (P : MachineData → Prop) :
    ⦃P⦄ zipWithAddBinary ⪯[ofStateRepr id] zipWithAdd ⦃fun _ _ _ => True; fun a a' _ => a = a'⦄ :=
  Binary.refines_program zipWithAddBinary_decodesTo zipWithAddBinary_labels zipWithAddBinary_symbols
    zipWithAddBinary_entry zipWithAddBinary_stop P

variable (s : MachineData) (ra : Int64)

theorem zipWithAddBinary_refines_P {A B O : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    ⦃(· = s.push64 ra)⦄ zipWithAddBinary
      ⪯[(ofStateRepr id).comp (machineToArray O n)]
      (zipWithAddP (words (s.push64 ra).dmem A n).toArray (words (s.push64 ra).dmem B n).toArray)
      ⦃fun _ _ _ => False; fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        outView O n t.dmem = Id.run (zipWithAddP (words (s.push64 ra).dmem A n).toArray
          (words (s.push64 ra).dmem B n).toArray)⦄ :=
  Refinement.comp_le (by grind) (by grind) (by grind)
    (zipWithAdd_refines_P s ra hrdi hrsi hrdx hrcx hmem) (zipWithAddBinary_refines_zipWithAdd _)

theorem zipWithAddBinary_correct {A B O : BitVec 64} {n : Nat}
    (hrdi : (s.push64 ra).regs.get64 .rdi = A) (hrsi : (s.push64 ra).regs.get64 .rsi = B)
    (hrdx : (s.push64 ra).regs.get64 .rdx = O) (hrcx : (s.push64 ra).regs.get64 .rcx = BitVec.ofNat 64 n)
    (hmem : ZipArrays (s.push64 ra).dmem A B O ((s.push64 ra).regs.get64 .rsp) n) :
    Triple zipWithAddBinary (fun t => t = s.push64 ra) (fun _ _ => True)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp
        ∧ words t.dmem O n = List.zipWith (· + ·) (words (s.push64 ra).dmem A n)
            (words (s.push64 ra).dmem B n)) := by
  have h := (zipWithAddBinary_refines_P s ra hrdi hrsi hrdx hrcx hmem).transport
    (Pa := True) (Qa := fun _ => True) (Ea := estack⟨⟩) ⟨fun _ => trivial⟩
  refine ⟨fun t ht => WP.wp_monotone (x := zipWithAddBinary) (fun _ _ _ => trivial) ?_ t
    (h.le_wp t (by simp only [meet_apply, meet_prop_eq_and, Concretization.comp_pred,
      ofStateRepr_pred, purify_pred]; exact ⟨ht, trivial⟩))⟩
  rintro a t ⟨hra, hrsp, ho⟩
  exact ⟨hra, hrsp, words_eq_zipWith_of_outView ho⟩

end

end Ascent.Kraken
