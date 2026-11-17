import Demo.Kraken.Syntax

/-!
# The blocks of a text

The declarations of this module mirror the exported API of kraken's `Kraken.Blocks` and of the
syntactic part of `Kraken.StateCfg`, under kraken's names. `Program.Block` is a structure, because
the demo builds and projects blocks. The operations on texts are opaque, and the axioms state
kraken's theorems about them.

The axioms `Program.firstLabel_nil`, `Program.firstLabel_cons`, `Program.blockAt_def`,
`Program.entryBlock_def`, `Program.fromNext_some` and `Program.fromNext_none` are not theorems of
kraken. They state kraken's definitions, which `Demo.CfgGhost` and the simp sets of the demo use.
-/

opaque Program.fromLabel : Program → Label → Program

opaque Program.straight (p : Program) : Program

@[vcgen_simp] axiom Program.straight_nil : Program.straight [] = []

@[vcgen_simp] axiom Program.straight_cons_instr (i : Instr) (p : Program) :
    Program.straight (.instr i :: p) = .instr i :: Program.straight p

@[vcgen_simp] axiom Program.straight_cons_label (l : Label) (p : Program) :
    Program.straight (.label l :: p) = Program.straight p

@[vcgen_simp] axiom Program.straight_cons_byteArray (a : ByteArray) (p : Program) :
    Program.straight (.byteArray a :: p) = .byteArray a :: Program.straight p

opaque Program.view : Program → Program × List (Label × Program)

axiom Program.labels_view (p : Program) :
    Program.labels p = (Program.view p).2.map (·.1)

structure Program.Block where
  label : Option Label
  idx : Nat
  body : Program
  next : Option Label
  deriving Inhabited

opaque Program.firstLabel : List (Label × Program) → Option Label

axiom Program.firstLabel_nil : Program.firstLabel [] = none

axiom Program.firstLabel_cons (l : Label) (b : Program) (bs : List (Label × Program)) :
    Program.firstLabel ((l, b) :: bs) = some l

opaque Program.blockAtAux (j : Nat) : List (Label × Program) → Label → Option Program.Block

opaque Program.blockAt (p : Program) (l : Label) : Option Program.Block

axiom Program.blockAt_def (p : Program) (l : Label) :
    Program.blockAt p l = Program.blockAtAux 1 (Program.view p).2 l

opaque Program.entryBlock (p : Program) : Program.Block

axiom Program.entryBlock_def (p : Program) :
    Program.entryBlock p = ⟨none, 0, (Program.view p).1, Program.firstLabel (Program.view p).2⟩

opaque Program.blockIdx (p : Program) (l : Label) : Nat

axiom Program.isSome_blockAt_of_mem {p : Program} {l : Label} (h : l ∈ Program.labels p) :
    (Program.blockAt p l).isSome

axiom Program.blockAtAux_spec : ∀ {j : Nat} {bs : List (Label × Program)} {l : Label}
    {blk : Program.Block}, Program.blockAtAux j bs l = some blk →
    blk.label = some l ∧ ∃ i, bs[i]? = some (l, blk.body)
      ∧ blk.next = Program.firstLabel (bs.drop (i + 1)) ∧ blk.idx = j + i

axiom Program.blockAtAux_of_getElem : ∀ {j : Nat} {bs : List (Label × Program)}
    (_ : (bs.map (·.1)).Nodup) {i : Nat} {l : Label} {b : Program},
    bs[i]? = some (l, b) →
    Program.blockAtAux j bs l = some ⟨some l, j + i, b, Program.firstLabel (bs.drop (i + 1))⟩

axiom Program.fromLabel_split {p : Program} {l : Label}
    (hnd : (Program.labels p).Nodup) (hne : Program.fromLabel p l ≠ []) :
    ∃ t rest, p = t ++ (Directive.label l :: rest)
      ∧ Program.fromLabel p l = Directive.label l :: rest
      ∧ l ∉ Program.labels t
      ∧ t.length = p.length - (Program.fromLabel p l).length

axiom Program.blockAt_next {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk)
    {l' : Label} (hn : blk.next = some l') :
    (Program.blockAt p l').isSome ∧ Program.blockIdx p l' = Program.blockIdx p l + 1

opaque Program.blocksFrom (b : Option Label) (j : Nat) (body : Program) :
    List (Label × Program) → List Program.Block

opaque Program.blocks (p : Program) : List Program.Block

axiom Program.entryBlock_mem_blocks (p : Program) : Program.entryBlock p ∈ Program.blocks p

axiom Program.mem_blocks_of_blockAt {p : Program} {l : Label} {blk : Program.Block}
    (hb : Program.blockAt p l = some blk) : blk ∈ Program.blocks p

@[vcgen_simp] axiom Program.view_nil : Program.view [] = ([], [])

@[vcgen_simp] axiom Program.view_cons_label (l : Label) (p : Program) :
    Program.view (.label l :: p) = ([], (l, (Program.view p).1) :: (Program.view p).2)

@[vcgen_simp] axiom Program.view_cons_instr (i : Instr) (p : Program) :
    Program.view (.instr i :: p) = (.instr i :: (Program.view p).1, (Program.view p).2)

@[vcgen_simp] axiom Program.blocks_eq (p : Program) :
    Program.blocks p = Program.blocksFrom none 0 (Program.view p).1 (Program.view p).2

@[vcgen_simp] axiom Program.blocksFrom_nil (b : Option Label) (j : Nat) (body : Program) :
    Program.blocksFrom b j body [] = [⟨b, j, Program.straight body, none⟩]

@[vcgen_simp] axiom Program.blocksFrom_cons (b : Option Label) (j : Nat) (body : Program) (l : Label)
    (body' : Program) (bs : List (Label × Program)) :
    Program.blocksFrom b j body ((l, body') :: bs)
      = ⟨b, j, Program.straight body, some l⟩ :: Program.blocksFrom (some l) (j + 1) body' bs

opaque Program.fromNext (p : Program) : Option Label → Program

axiom Program.fromNext_some (p : Program) (l : Label) : Program.fromNext p (some l) = Program.fromLabel p l

axiom Program.fromNext_none (p : Program) : Program.fromNext p none = []

axiom Program.fromLabel_block {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk) :
    Program.fromLabel p l = Directive.label l :: (blk.body ++ Program.fromNext p blk.next)

axiom Program.view_eq_entry {p : Program} (hnd : (Program.labels p).Nodup) :
    p = (Program.view p).1 ++ Program.fromNext p (Program.entryBlock p).next

axiom Program.drop_fromLabel (p : Program) (l : Label) :
    p.drop (p.length - (Program.fromLabel p l).length) = Program.fromLabel p l
