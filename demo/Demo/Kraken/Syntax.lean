/-!
# The syntax of kraken's x64 texts

The declarations of this module mirror the exported API of kraken's `Kraken.X64.Syntax` and
`Kraken.Layout`, under kraken's names. The inductive types keep the constructors that the demo
uses. The operations on executables are opaque, and the axioms state kraken's theorems about them.

`Program.labels` is kraken's definition, with kraken's proofs of its theorems: the demo decides
the membership of a label in the labels of a literal text by `decide +kernel`.

The axioms `Kraken.Layout.apply_def`, `Kraken.Executable.withAddresses_nil`,
`Kraken.Executable.withAddresses_cons`, `Kraken.Executable.directivesAtAddress_def`,
`Kraken.Executable.sizeBefore_def` and `Kraken.Executable.addrOf_def` are not theorems of kraken.
They state kraken's definitions, which `Demo.Binary` and `Demo.BinaryCheck` unfold.
-/

inductive Width | W8 | W16 | W32 | W64 deriving DecidableEq

namespace Width
@[simp, reducible] def bits : Width → Nat | W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64
abbrev type (w : Width) : Type := BitVec w.bits
end Width

inductive Reg64
  | rax | rbx | rcx | rdx
  | rsi | rdi | rsp | rbp
  | r8  | r9  | r10 | r11
  | r12 | r13 | r14 | r15
  deriving DecidableEq

inductive Reg : Width → Type
  | low (_ : Reg64) (w : Width) : Reg w
  deriving DecidableEq

abbrev Label := String

inductive ConstExpr
  | label (_ : Label)
  | int64 (_ : Int64)
  | after_current_instruction
  | sub (_ _ : ConstExpr)
  deriving DecidableEq

inductive RegOrRip where | reg (_ : Reg64)
  deriving DecidableEq

structure AddrIndex where
  reg : Reg64
  scale: Width
  deriving DecidableEq

structure AddrExpr where
  base : Option RegOrRip
  idx : Option AddrIndex
  disp : ConstExpr := .int64 0
  deriving DecidableEq

inductive RegOrMem w | reg (r : Reg w) | mem (_ : AddrExpr)
  deriving DecidableEq
abbrev Dst := RegOrMem

inductive Operand w | regOrMem (_ : RegOrMem w) | imm (v : ConstExpr)
  deriving DecidableEq

inductive CondCode | o | no | c | nc | z | nz | be | a | s | ns | p | np | l | ge | le | g
  deriving DecidableEq

inductive ShiftCountExpr | imm8 (v : ConstExpr)
  deriving DecidableEq

inductive RelRegOrMem | rel (_ : ConstExpr)
  deriving DecidableEq

inductive Operation (w : Width)
  | mov (_ : Dst w) (src : Operand w)
  | movzx {w'} (_ : Dst w) (src : RegOrMem w')
  | push (src : Operand w)
  | pop  (_ : Dst w)
  | lea (_ : Reg w) (src : AddrExpr)
  | add  (_ : Dst w) (src : Operand w)
  | inc  (_ : RegOrMem w)
  | dec  (_ : RegOrMem w)
  | sub  (_ : Dst w) (src : Operand w)
  | cmp  (a : RegOrMem w) (b : Operand w)
  | test (a : RegOrMem w) (b : Operand w)
  | xor  (_ : Dst w) (src : Operand w)
  | shr  (_ : Dst w) (_ : ShiftCountExpr)
  | jcc (cc : CondCode) (target : Label)
  | jmp (target : RelRegOrMem)
  | call (target : RelRegOrMem)
  | ret
  | nop (length : Nat)
  | nopalign (alignment : Nat) (pad : Option Nat)
  deriving DecidableEq

inductive Instr
  | regular (address_size : Width) (operation_size : Width) (operation : Operation operation_size)
  deriving DecidableEq

inductive Directive
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (_ : ByteArray)
  deriving DecidableEq

abbrev Program := List Directive

def Directive.label? : Directive → Option Label
  | .label l => some l
  | _ => none

def Program.labels (p : Program) : List Label := p.filterMap Directive.label?

@[simp, grind =] theorem Program.labels_nil : Program.labels [] = [] := rfl

@[simp, grind =] theorem Program.labels_cons_instr (i : Instr) (p : Program) :
    Program.labels (.instr i :: p) = Program.labels p := rfl

theorem Program.mem_labels {p : Program} {l : Label} : l ∈ Program.labels p ↔ Directive.label l ∈ p := by
  rw [Program.labels, List.mem_filterMap]
  constructor
  · rintro ⟨d, hd, hl⟩
    cases d <;> simp_all [Directive.label?]
  · exact fun h => ⟨_, h, rfl⟩

namespace Kraken

structure Sized (Directive : Type) where
  directive : Directive
  size : Nat

structure Executable (Directive : Type) where
  startAddr : Int64
  program : List (Sized Directive)
  deriving Inhabited

class Layout (Directive : Type) where
  start : Int64
  size : Nat → Nat

opaque Layout.apply {Directive : Type} (l : Layout Directive) (prog : List Directive) :
    Executable Directive

axiom Layout.apply_def {Directive : Type} (l : Layout Directive) (prog : List Directive) :
    l.apply prog = {startAddr := l.start, program := prog.mapIdx (fun i directive => {directive, size := l.size i})}

structure Addressable (Directive : Type) extends Sized Directive where (addr : Int64)

opaque Executable.withAddresses {Directive : Type} (e : Executable Directive) :
    List (Addressable Directive)

axiom Executable.withAddresses_nil {Directive : Type} (startAddr : Int64) :
    Executable.withAddresses ({startAddr, program := []} : Executable Directive) = []

axiom Executable.withAddresses_cons {Directive : Type} (startAddr : Int64) (instr : Sized Directive)
    (program : List (Sized Directive)) :
    Executable.withAddresses ({startAddr, program := instr :: program} : Executable Directive) =
      {instr with addr := startAddr} ::
        Executable.withAddresses {startAddr := startAddr + .ofNat instr.size, program}

opaque Executable.directivesAtAddress {Directive : Type} (e : Executable Directive) (a : Int64) :
    List (Sized Directive)

axiom Executable.directivesAtAddress_def {Directive : Type} (e : Executable Directive) (a : Int64) :
    e.directivesAtAddress a =
      ((e.withAddresses.dropWhile (·.addr ≠ a)).takeWhile (·.addr = a)).map (·.toSized)

opaque Executable.sizeBefore {Directive : Type} (e : Executable Directive) (n : Nat) : Nat

axiom Executable.sizeBefore_def {Directive : Type} (e : Executable Directive) (n : Nat) :
    e.sizeBefore n = ((e.program.take n).map (·.size)).sum

opaque Executable.addrOf {Directive : Type} (e : Executable Directive) (n : Nat) : Int64

axiom Executable.addrOf_def {Directive : Type} (e : Executable Directive) (n : Nat) :
    e.addrOf n = e.startAddr + .ofNat (e.sizeBefore n)

axiom Executable.mem_of_mem_directivesAtAddress {Directive : Type} {e : Executable Directive}
    {a : Int64} {c : Sized Directive} (h : c ∈ e.directivesAtAddress a) : c ∈ e.program

axiom Executable.getElem?_withAddresses_eq {Directive : Type} (e : Executable Directive) (k : Nat) :
    e.withAddresses[k]? = e.program[k]?.map (fun c => {c with addr := e.addrOf k})

@[grind hom] theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

end Kraken

abbrev Executable := Kraken.Executable Directive
