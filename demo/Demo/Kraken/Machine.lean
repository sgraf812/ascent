import Demo.Kraken.Syntax
import Demo.Kraken.Mem

/-!
# The x64 machine state

The declarations of this module mirror the exported API of kraken's `Kraken.X64.Semantics`,
`Kraken.X64.Registers` and `Kraken.Specs`, under kraken's names. The register file, the flags, the
machine state and the effects of a step are structures and inductive types, because the demo builds
and projects them. `RegZmms` keeps one of kraken's 32 vector registers. `BitVec.take`,
`CondCode.interp`, `Directives.interp` and `Executable.labels` are kraken's definitions. The other
operations are opaque, and the axioms state kraken's theorems about them.

These axioms are not theorems of kraken:

* `Effects.all_done` states the case of kraken's `Effects.All` for the one constructor of
  `Effects` in this module. The other cases of kraken's `Effects.All` need the other constructors
  of kraken's `Effects`.
* `Directive.interp_test_labels` and the other axioms of the section on label maps state that the
  step of an instruction reads the label map only at its jump target. `Demo.Binary` uses them for
  the instructions of its decoder.
-/

namespace BitVec

def take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n

theorem take_def {w} (x : BitVec w) (n : Nat) : x.take n = x.extractLsb' 0 n := rfl

opaque cpop_ {w} (x : BitVec w) : BitVec w

end BitVec

opaque BitVec.replaceLow {w n} (old : BitVec w) (new : BitVec n) : BitVec w

structure Reg64s where
  rax : UInt64 := 0
  rbx : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  rsi : UInt64 := 0
  rdi : UInt64 := 0
  rsp : UInt64 := 0
  rbp : UInt64 := 0
  r8  : UInt64 := 0
  r9  : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0
  deriving Inhabited

opaque Reg64s.get64 (s : Reg64s) (r : Reg64) : BitVec 64

opaque Reg64s.set64 (regs : Reg64s) (r : Reg64) (v : BitVec 64) : Reg64s

opaque Reg64s.get (s : Reg64s) {w} (r : Reg w) : w.type

opaque Reg64s.set (s : Reg64s) {w} (r : Reg w) (v : w.type) : Reg64s

structure RegZmms where
  zmm0 : BitVec 512 := 0#512
  deriving Inhabited

structure StatusFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving Inhabited

abbrev DataMem := Mem 64

structure MachineData where
  regs : Reg64s
  zmms : RegZmms
  status : StatusFlags
  dmem : DataMem
  deriving Inhabited

structure MachineState where
  data : MachineData
  pc : Int64
  deriving Inhabited

inductive Effects
  | done (a : MachineState)
  deriving Inhabited

opaque Effects.All (post : MachineState → Prop) : Effects → Prop

axiom Effects.all_done (post : MachineState → Prop) (a : MachineState) : (Effects.done a).All post = post a

class Labels where label : Label → Int64
  deriving Inhabited
export Labels (label)

def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .o  => s.of | .no => !s.of
  | .c  => s.cf | .nc => !s.cf
  | .z  => s.zf | .nz => !s.zf
  | .be => s.cf || s.zf | .a  => !s.cf && !s.zf
  | .s  => s.sf | .ns => !s.sf
  | .p  => s.pf | .np => !s.pf
  | .l  => s.sf != s.of | .ge => s.sf == s.of
  | .le => (s.sf != s.of) || s.zf | .g  => !s.zf && (s.sf == s.of)

structure StatusFlags.from_result.Remaining where
  cf : Bool
  af : Bool
  of : Bool

opaque StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags

@[simp, vcgen_simp] axiom StatusFlags.cf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).cf = f.cf
grind_pattern StatusFlags.cf_from_result => (StatusFlags.from_result v f).cf

@[simp, vcgen_simp] axiom StatusFlags.zf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).zf = (v == BitVec.zero w)
grind_pattern StatusFlags.zf_from_result => (StatusFlags.from_result v f).zf

@[simp, vcgen_simp] axiom StatusFlags.sf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).sf = v.msb

@[simp, vcgen_simp] axiom StatusFlags.pf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).pf = ((v.take 8).cpop_ % 2 == BitVec.zero _)

@[simp, vcgen_simp] axiom StatusFlags.of_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).of = f.of

opaque Directive.interp [Labels]
  (d : Directive) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects

def Directives.interp [Labels]
  (ds : List (Kraken.Sized Directive)) (s : MachineData) (pc : Int64)
  (ret : Int64 → MachineData → Effects) (jmp : Int64 → MachineData → Effects := ret) : Effects :=
  match ds with
  | [] => ret pc s
  | {directive, size := sz} :: ds =>
    directive.interp s (.mk pc (pc+.ofNat sz)) (jmp:=jmp) (next := (fun s =>
    interp ds s (pc+.ofNat sz) ret jmp))

theorem Directives.interp_nil [Labels] (s : MachineData) (pc : Int64)
    (ret jmp : Int64 → MachineData → Effects) : Directives.interp [] s pc ret jmp = ret pc s := rfl

theorem Directives.interp_cons [Labels] (directive : Directive) (sz : Nat) (ds : List (Kraken.Sized Directive))
    (s : MachineData) (pc : Int64) (ret jmp : Int64 → MachineData → Effects) :
    Directives.interp ({directive, size := sz} :: ds) s pc ret jmp =
      directive.interp s (.mk pc (pc + .ofNat sz)) (jmp := jmp)
        (next := fun s => Directives.interp ds s (pc + .ofNat sz) ret jmp) := rfl

abbrev Layout := Kraken.Layout Directive

@[reducible]
def Executable.labels (e : Executable) : Labels :=
  { label l := (e.withAddresses.findSome?
      (fun {directive, addr, ..} => if directive = .label l then .some addr else .none)).getD (-1) }

theorem Executable.labels_def (e : Executable) (l : Label) :
    (Executable.labels e).label l =
      (e.withAddresses.findSome? (fun x => if x.directive = .label l then some x.addr else none)).getD (-1) :=
  rfl

/-! ## Label maps

The step of an instruction without labels reads no label map, and the step of a conditional jump
reads the label map only at its target. -/

section
variable (L L' : Labels) (asz osz : Width)

axiom Directive.interp_test_labels (ra rb : Reg osz) :
    @Directive.interp L (.instr (.regular asz osz (.test (.reg ra) (.regOrMem (.reg rb))))) =
      @Directive.interp L' (.instr (.regular asz osz (.test (.reg ra) (.regOrMem (.reg rb)))))

axiom Directive.interp_cmp_labels (ra rb : Reg osz) :
    @Directive.interp L (.instr (.regular asz osz (.cmp (.reg ra) (.regOrMem (.reg rb))))) =
      @Directive.interp L' (.instr (.regular asz osz (.cmp (.reg ra) (.regOrMem (.reg rb)))))

axiom Directive.interp_xor_labels (ra rb : Reg osz) :
    @Directive.interp L (.instr (.regular asz osz (.xor (.reg ra) (.regOrMem (.reg rb))))) =
      @Directive.interp L' (.instr (.regular asz osz (.xor (.reg ra) (.regOrMem (.reg rb)))))

axiom Directive.interp_inc_labels (r : Reg osz) :
    @Directive.interp L (.instr (.regular asz osz (.inc (.reg r)))) =
      @Directive.interp L' (.instr (.regular asz osz (.inc (.reg r))))

axiom Directive.interp_mov_load_labels (r : Reg osz) (b : Option RegOrRip) (i : Option AddrIndex)
    (d : Int64) :
    @Directive.interp L (.instr (.regular asz osz (.mov (.reg r) (.regOrMem (.mem ⟨b, i, .int64 d⟩))))) =
      @Directive.interp L' (.instr (.regular asz osz (.mov (.reg r) (.regOrMem (.mem ⟨b, i, .int64 d⟩)))))

axiom Directive.interp_add_load_labels (r : Reg osz) (b : Option RegOrRip) (i : Option AddrIndex)
    (d : Int64) :
    @Directive.interp L (.instr (.regular asz osz (.add (.reg r) (.regOrMem (.mem ⟨b, i, .int64 d⟩))))) =
      @Directive.interp L' (.instr (.regular asz osz (.add (.reg r) (.regOrMem (.mem ⟨b, i, .int64 d⟩)))))

axiom Directive.interp_mov_store_labels (r : Reg osz) (b : Option RegOrRip) (i : Option AddrIndex)
    (d : Int64) :
    @Directive.interp L (.instr (.regular asz osz (.mov (.mem ⟨b, i, .int64 d⟩) (.regOrMem (.reg r))))) =
      @Directive.interp L' (.instr (.regular asz osz (.mov (.mem ⟨b, i, .int64 d⟩) (.regOrMem (.reg r)))))

axiom Directive.interp_ret_labels :
    @Directive.interp L (.instr (.regular asz osz .ret)) =
      @Directive.interp L' (.instr (.regular asz osz .ret))

axiom Directive.interp_jcc_labels (cc : CondCode) (l l' : Label) (h : L.label l = L'.label l') :
    @Directive.interp L (.instr (.regular asz osz (.jcc cc l))) =
      @Directive.interp L' (.instr (.regular asz osz (.jcc cc l')))

end

/-! ## Memory accesses of the data memory -/

@[vcgen_simp] axiom Mem.loadInt_storeInt_8 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 1 v).loadInt a 1 = some (Int.ofBytes (Int.toBytes 1 v))
grind_pattern Mem.loadInt_storeInt_8 => (m.storeInt a 1 v).loadInt a 1

@[vcgen_simp] axiom BitVec.ofInt_ofBytes_toBytes_8 (v : Int) :
    BitVec.ofInt 8 (Int.ofBytes (Int.toBytes 1 v)) = BitVec.ofInt 8 v

@[vcgen_simp] axiom Mem.loadInt_storeInt_16 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 2 v).loadInt a 2 = some (Int.ofBytes (Int.toBytes 2 v))
grind_pattern Mem.loadInt_storeInt_16 => (m.storeInt a 2 v).loadInt a 2

@[vcgen_simp] axiom BitVec.ofInt_ofBytes_toBytes_16 (v : Int) :
    BitVec.ofInt 16 (Int.ofBytes (Int.toBytes 2 v)) = BitVec.ofInt 16 v

@[vcgen_simp] axiom Mem.loadInt_storeInt_64 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 8 v).loadInt a 8 = some (Int.ofBytes (Int.toBytes 8 v))
grind_pattern Mem.loadInt_storeInt_64 => (m.storeInt a 8 v).loadInt a 8

@[vcgen_simp] axiom BitVec.ofInt_ofBytes_toBytes_64 (v : Int) :
    BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v)) = BitVec.ofInt 64 v

grind_pattern BitVec.ofInt_ofBytes_toBytes_8 => Option.get! (some (Int.ofBytes (Int.toBytes 1 v)))
grind_pattern BitVec.ofInt_ofBytes_toBytes_16 => Option.get! (some (Int.ofBytes (Int.toBytes 2 v)))
grind_pattern BitVec.ofInt_ofBytes_toBytes_64 => Option.get! (some (Int.ofBytes (Int.toBytes 8 v)))

/-! ## Registers -/

@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_rax (s : Reg64s) : s.get64 .rax = s.rax.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_rbx (s : Reg64s) : s.get64 .rbx = s.rbx.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_rcx (s : Reg64s) : s.get64 .rcx = s.rcx.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_rdx (s : Reg64s) : s.get64 .rdx = s.rdx.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_rsi (s : Reg64s) : s.get64 .rsi = s.rsi.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_rdi (s : Reg64s) : s.get64 .rdi = s.rdi.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_rsp (s : Reg64s) : s.get64 .rsp = s.rsp.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_rbp (s : Reg64s) : s.get64 .rbp = s.rbp.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_r8 (s : Reg64s) : s.get64 .r8 = s.r8.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_r9 (s : Reg64s) : s.get64 .r9 = s.r9.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_r10 (s : Reg64s) : s.get64 .r10 = s.r10.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_r11 (s : Reg64s) : s.get64 .r11 = s.r11.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_r12 (s : Reg64s) : s.get64 .r12 = s.r12.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_r13 (s : Reg64s) : s.get64 .r13 = s.r13.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_r14 (s : Reg64s) : s.get64 .r14 = s.r14.toBitVec
@[simp, grind norm, vcgen_simp] axiom Reg64s.get64_r15 (s : Reg64s) : s.get64 .r15 = s.r15.toBitVec

@[vcgen_simp] axiom Reg64s.set_low_W32 (s : Reg64s) (r : Reg64) (v : BitVec 32) :
    Reg64s.set s (.low r .W32) v = s.set64 r (v.zeroExtend 64)

@[vcgen_simp] axiom Reg64s.set_low_W16 (s : Reg64s) (r : Reg64) (v : BitVec 16) :
    Reg64s.set s (.low r .W16) v = s.set64 r ((s.get64 r).replaceLow v)

@[vcgen_simp] axiom Reg64s.set_low_W8 (s : Reg64s) (r : Reg64) (v : BitVec 8) :
    Reg64s.set s (.low r .W8) v = s.set64 r ((s.get64 r).replaceLow v)

@[vcgen_simp] axiom Reg64s.get_low_W16 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W16) = (s.get64 r).take 16

@[vcgen_simp] axiom Reg64s.get_low_W8 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W8) = (s.get64 r).take 8

@[vcgen_simp] axiom BitVec.take_replaceLow_8 (x : BitVec 64) (v : BitVec 8) :
    (x.replaceLow v).take 8 = v

@[vcgen_simp] axiom Reg64s.set64_rax (s : Reg64s) (v : BitVec 64) :
    s.set64 .rax v = { s with rax := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_rbx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rbx v = { s with rbx := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_rcx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rcx v = { s with rcx := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_rdx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rdx v = { s with rdx := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_rsi (s : Reg64s) (v : BitVec 64) :
    s.set64 .rsi v = { s with rsi := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_rdi (s : Reg64s) (v : BitVec 64) :
    s.set64 .rdi v = { s with rdi := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_rsp (s : Reg64s) (v : BitVec 64) :
    s.set64 .rsp v = { s with rsp := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_r8 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r8 v = { s with r8 := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_r9 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r9 v = { s with r9 := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_r10 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r10 v = { s with r10 := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_r11 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r11 v = { s with r11 := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_r12 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r12 v = { s with r12 := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_r14 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r14 v = { s with r14 := .ofBitVec v }
@[vcgen_simp] axiom Reg64s.set64_r15 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r15 v = { s with r15 := .ofBitVec v }

@[simp, vcgen_simp] theorem Reg64s.rax_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rax = a0 := rfl
@[simp, vcgen_simp] theorem Reg64s.rbx_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rbx = a1 := rfl
@[simp, vcgen_simp] theorem Reg64s.rcx_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rcx = a2 := rfl
@[simp, vcgen_simp] theorem Reg64s.rdx_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rdx = a3 := rfl
@[simp, vcgen_simp] theorem Reg64s.rsi_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rsi = a4 := rfl
@[simp, vcgen_simp] theorem Reg64s.rdi_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rdi = a5 := rfl
@[simp, vcgen_simp] theorem Reg64s.rsp_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rsp = a6 := rfl
@[simp, vcgen_simp] theorem Reg64s.r8_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r8 = a8 := rfl
@[simp, vcgen_simp] theorem Reg64s.r9_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r9 = a9 := rfl
@[simp, vcgen_simp] theorem Reg64s.r12_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r12 = a12 := rfl
@[simp, vcgen_simp] theorem Reg64s.r14_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r14 = a14 := rfl
@[simp, vcgen_simp] theorem Reg64s.r15_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r15 = a15 := rfl

@[simp] axiom Reg64s.get64_set64 (s : Reg64s) (r r' : Reg64) (v : BitVec 64) :
    (s.set64 r v).get64 r' = if r' = r then v else s.get64 r'
grind_pattern Reg64s.get64_set64 => (s.set64 r v).get64 r'

@[simp] axiom Reg64s.rbx_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rbx = if r = .rbx then .ofBitVec v else s.rbx
grind_pattern Reg64s.rbx_set64 => (s.set64 r v).rbx
@[simp] axiom Reg64s.rsi_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rsi = if r = .rsi then .ofBitVec v else s.rsi
grind_pattern Reg64s.rsi_set64 => (s.set64 r v).rsi
@[simp] axiom Reg64s.rdi_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rdi = if r = .rdi then .ofBitVec v else s.rdi
grind_pattern Reg64s.rdi_set64 => (s.set64 r v).rdi
@[simp] axiom Reg64s.rsp_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rsp = if r = .rsp then .ofBitVec v else s.rsp
grind_pattern Reg64s.rsp_set64 => (s.set64 r v).rsp
@[simp] axiom Reg64s.rbp_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rbp = if r = .rbp then .ofBitVec v else s.rbp
grind_pattern Reg64s.rbp_set64 => (s.set64 r v).rbp
@[simp] axiom Reg64s.r12_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r12 = if r = .r12 then .ofBitVec v else s.r12
grind_pattern Reg64s.r12_set64 => (s.set64 r v).r12
@[simp] axiom Reg64s.r13_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r13 = if r = .r13 then .ofBitVec v else s.r13
grind_pattern Reg64s.r13_set64 => (s.set64 r v).r13
@[simp] axiom Reg64s.r14_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r14 = if r = .r14 then .ofBitVec v else s.r14
grind_pattern Reg64s.r14_set64 => (s.set64 r v).r14
@[simp] axiom Reg64s.r15_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r15 = if r = .r15 then .ofBitVec v else s.r15
grind_pattern Reg64s.r15_set64 => (s.set64 r v).r15

@[grind =] theorem BitVec.toNat_sub_le {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

/-! ## Flags and condition codes -/

opaque StatusFlags.ofSub {w} (a b : BitVec w) : StatusFlags

opaque StatusFlags.ofAdd {w} (a b : BitVec w) : StatusFlags

opaque StatusFlags.ofDec (a : BitVec 64) (cf : Bool) : StatusFlags

opaque StatusFlags.ofInc (a : BitVec 64) (cf : Bool) : StatusFlags

opaque StatusFlags.ofLogic {w} (v : BitVec w) (af : Bool) : StatusFlags

opaque StatusFlags.neg (s : StatusFlags) : Bool

@[simp] theorem CondCode.interp_z (s : StatusFlags) :
    CondCode.z.interp s = s.zf := rfl
grind_pattern CondCode.interp_z => CondCode.z.interp s
@[simp] theorem CondCode.interp_nz (s : StatusFlags) :
    CondCode.nz.interp s = !s.zf := rfl
grind_pattern CondCode.interp_nz => CondCode.nz.interp s
@[simp] theorem CondCode.interp_c (s : StatusFlags) :
    CondCode.c.interp s = s.cf := rfl
grind_pattern CondCode.interp_c => CondCode.c.interp s
@[simp] theorem CondCode.interp_nc (s : StatusFlags) :
    CondCode.nc.interp s = !s.cf := rfl
grind_pattern CondCode.interp_nc => CondCode.nc.interp s
@[simp] theorem CondCode.interp_a (s : StatusFlags) :
    CondCode.a.interp s = (!s.cf && !s.zf) := rfl
grind_pattern CondCode.interp_a => CondCode.a.interp s
@[simp] theorem CondCode.interp_be (s : StatusFlags) :
    CondCode.be.interp s = (s.cf || s.zf) := rfl
grind_pattern CondCode.interp_be => CondCode.be.interp s

@[simp] theorem CondCode.interp_l (s : StatusFlags) :
    CondCode.l.interp s = (s.sf != s.of) := rfl
@[simp] theorem CondCode.interp_le (s : StatusFlags) :
    CondCode.le.interp s = ((s.sf != s.of) || s.zf) := rfl
@[simp] theorem CondCode.interp_ge (s : StatusFlags) :
    CondCode.ge.interp s = (s.sf == s.of) := rfl
@[simp] theorem CondCode.interp_g (s : StatusFlags) :
    CondCode.g.interp s = (!s.zf && (s.sf == s.of)) := rfl

theorem CondCode.interp_o (s : StatusFlags) : CondCode.o.interp s = s.of := rfl
theorem CondCode.interp_no (s : StatusFlags) : CondCode.no.interp s = !s.of := rfl
theorem CondCode.interp_s (s : StatusFlags) : CondCode.s.interp s = s.sf := rfl
theorem CondCode.interp_ns (s : StatusFlags) : CondCode.ns.interp s = !s.sf := rfl
theorem CondCode.interp_p (s : StatusFlags) : CondCode.p.interp s = s.pf := rfl
theorem CondCode.interp_np (s : StatusFlags) : CondCode.np.interp s = !s.pf := rfl

axiom CondCode.interp_l_neg (s : StatusFlags) : CondCode.l.interp s = s.neg
grind_pattern CondCode.interp_l_neg => CondCode.l.interp s
axiom CondCode.interp_ge_neg (s : StatusFlags) :
    CondCode.ge.interp s = !s.neg
grind_pattern CondCode.interp_ge_neg => CondCode.ge.interp s
axiom CondCode.interp_le_neg (s : StatusFlags) :
    CondCode.le.interp s = (s.neg || s.zf)
grind_pattern CondCode.interp_le_neg => CondCode.le.interp s
axiom CondCode.interp_g_neg (s : StatusFlags) :
    CondCode.g.interp s = (!s.neg && !s.zf)
grind_pattern CondCode.interp_g_neg => CondCode.g.interp s

theorem BitVec.usubOverflow_eq_true_iff {w} (a b : BitVec w) :
    BitVec.usubOverflow a b = true ↔ a.toNat < b.toNat := by
  simp [BitVec.usubOverflow]

@[simp, vcgen_simp] axiom StatusFlags.zf_ofSub {w} (a b : BitVec w) :
    (StatusFlags.ofSub a b).zf = (a - b == BitVec.zero w)
grind_pattern StatusFlags.zf_ofSub => (StatusFlags.ofSub a b).zf
@[simp, vcgen_simp] axiom StatusFlags.cf_ofSub {w} (a b : BitVec w) :
    (StatusFlags.ofSub a b).cf = BitVec.usubOverflow a b
grind_pattern StatusFlags.cf_ofSub => (StatusFlags.ofSub a b).cf

@[simp, vcgen_simp] axiom StatusFlags.sf_ofSub {w} (a b : BitVec w) :
    (StatusFlags.ofSub a b).sf = (a - b).msb
@[simp, vcgen_simp] axiom StatusFlags.of_ofSub {w} (a b : BitVec w) :
    (StatusFlags.ofSub a b).of = BitVec.ssubOverflow a b
@[simp, vcgen_simp] axiom StatusFlags.pf_ofSub {w} (a b : BitVec w) :
    (StatusFlags.ofSub a b).pf = (((a - b).take 8).cpop_ % 2 == BitVec.zero _)

axiom StatusFlags.neg_ofSub (a b : BitVec 64) : (StatusFlags.ofSub a b).neg = a.slt b

@[simp, vcgen_simp] axiom StatusFlags.cf_ofAdd {w} (a b : BitVec w) :
    (StatusFlags.ofAdd a b).cf = BitVec.uaddOverflow a b
grind_pattern StatusFlags.cf_ofAdd => (StatusFlags.ofAdd a b).cf

@[simp, vcgen_simp] axiom StatusFlags.zf_ofDec (a : BitVec 64) (cf : Bool) :
    (StatusFlags.ofDec a cf).zf = (a - 1 == BitVec.zero 64)

grind_pattern StatusFlags.zf_ofDec => (StatusFlags.ofDec a cf).zf

@[simp, vcgen_simp] axiom StatusFlags.zf_ofLogic {w} (v : BitVec w) (af : Bool) :
    (StatusFlags.ofLogic v af).zf = (v == BitVec.zero w)
grind_pattern StatusFlags.zf_ofLogic => (StatusFlags.ofLogic v af).zf
@[simp, vcgen_simp] axiom StatusFlags.cf_ofLogic {w} (v : BitVec w) (af : Bool) :
    (StatusFlags.ofLogic v af).cf = false
grind_pattern StatusFlags.cf_ofLogic => (StatusFlags.ofLogic v af).cf
@[simp, vcgen_simp] axiom StatusFlags.sf_ofLogic {w} (v : BitVec w) (af : Bool) :
    (StatusFlags.ofLogic v af).sf = v.msb
@[simp, vcgen_simp] axiom StatusFlags.of_ofLogic {w} (v : BitVec w) (af : Bool) :
    (StatusFlags.ofLogic v af).of = false
@[simp, vcgen_simp] axiom StatusFlags.pf_ofLogic {w} (v : BitVec w) (af : Bool) :
    (StatusFlags.ofLogic v af).pf = ((v.take 8).cpop_ % 2 == BitVec.zero _)
@[simp, vcgen_simp] axiom StatusFlags.af_ofLogic {w} (v : BitVec w) (af : Bool) :
    (StatusFlags.ofLogic v af).af = af
