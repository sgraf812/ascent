import Std.Data.ExtHashMap

/-!
# Memories and their blocks

The declarations of this module mirror the exported API of kraken's `Kraken.ToBytes`,
`Kraken.Mem` and `Kraken.SeparationMem`, under kraken's names. A memory is a finite map from
addresses to bytes. The operations on memories and byte lists are opaque, and the axioms state
kraken's theorems about them.

`Mem.Blocks.Inside`, `Mem.Blocks.Disjoint`, `Mem.Mapped` and the decision procedure
`Mem.Blocks.decInside` are kraken's definitions: the separation proofs of the demo unfold them,
and `FState.split` of `Demo.Frame` computes with the decision procedure.

The axioms `Int.take_def`, `Mem.loadInt_def` and `Mem.storeInt_def` are not theorems of kraken.
They state kraken's definitions, which the byte-level proofs of `Demo.Instr` and `Demo.Frame`
unfold.
-/

open Std

opaque Int.take (v : Int) (w : Nat) : Int

axiom Int.take_def (v : Int) (w : Nat) : v.take w = v % (2 : Int) ^ w

opaque Int.ofBytes (bs : List UInt8) : Int

opaque Int.toBytes (n : Nat) (v : Int) : List UInt8

axiom Int.toBytes_length (n : Nat) (v : Int) : (Int.toBytes n v).length = n
grind_pattern Int.toBytes_length => (Int.toBytes n v).length

axiom ofBytes_toBytes (n : Nat) (v : Int) : Int.ofBytes (Int.toBytes n v) = v.take (8 * n)

axiom BitVec.ofInt_ofBytes_toBytes (w : Nat) (n : Nat) (h_wn : w = 8 * n) (v : Int) :
    BitVec.ofInt w (Int.ofBytes (Int.toBytes n v)) = BitVec.ofInt w v

axiom Int.toBytes_emod (n : Nat) (x : Int) : Int.toBytes n (x.take (8 * n)) = Int.toBytes n x

abbrev Mem (w) := ExtHashMap (BitVec w) UInt8

opaque Mem.loadBytes {w} (m : Mem w) (a : BitVec w) (n : Nat) : Option (List UInt8)

opaque Mem.loadInt {w} (m : Mem w) (a : BitVec w) (n : Nat) : Option Int

axiom Mem.loadInt_def {w} (m : Mem w) (a : BitVec w) (n : Nat) :
    m.loadInt a n = (m.loadBytes a n).map Int.ofBytes

opaque List.At {w} (bs : List UInt8) (a : BitVec w) : ExtHashMap (BitVec w) UInt8

opaque Mem.storeBytes {w} (m : Mem w) (a : BitVec w) (bs : List UInt8) : Mem w

opaque Mem.storeInt {w} (m : Mem w) (a : BitVec w) (n : Nat) (v : Int) : Mem w

axiom Mem.storeInt_def {w} (m : Mem w) (a : BitVec w) (n : Nat) (v : Int) :
    m.storeInt a n v = m.storeBytes a (Int.toBytes n v)

axiom mem_At_iff {w} (bs : List UInt8) (a : BitVec w) (k : BitVec w) :
    k ∈ bs.At a ↔ ∃ i < bs.length, k = a + .ofNat w i

axiom Mem.loadInt_storeInt {w} (m : Mem w) (a : BitVec w) (n : Nat) (v : Int)
    (hw : n ≤ 2 ^ w) :
    (m.storeInt a n v).loadInt a n = some (Int.ofBytes (Int.toBytes n v))

axiom Mem.loadInt_congr {w} {m m' : Mem w} {a : BitVec w} {n : Nat}
    (h : ∀ i < n, m.get? (a + .ofNat w i) = m'.get? (a + .ofNat w i)) :
    m.loadInt a n = m'.loadInt a n

namespace Mem

def Blocks.Inside {w : Nat} (addr : BitVec w) (n : Nat) : List (BitVec w × Nat) → Prop
  | [] => False
  | (a, len) :: bs => (addr - a).toNat + n ≤ len ∨ Blocks.Inside addr n bs

axiom Blocks.Inside.base {w : Nat} {a : BitVec w} {n len : Nat} {bs : List (BitVec w × Nat)}
    (h : n ≤ len) : Blocks.Inside a n ((a, len) :: bs)

axiom Blocks.Inside.base_add {w : Nat} {a x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : x.toNat + n ≤ len) :
    Blocks.Inside (a + x) n ((a, len) :: bs)

axiom loadBytes_eq_some_iff {w : Nat} {m : Mem w} {a : BitVec w} {n : Nat} {bs : List UInt8} :
    m.loadBytes a n = some bs ↔
      bs.length = n ∧ ∀ i (h : i < bs.length), m.get? (a + .ofNat w i) = some bs[i]

def Mapped {w : Nat} (bs : List (BitVec w × Nat)) (m : Mem w) : Prop :=
  ∀ b, Blocks.Inside b 1 bs → (m.get? b).isSome

def Blocks.Disjoint {w : Nat} (bs bs' : List (BitVec w × Nat)) : Prop :=
  ∀ b, Blocks.Inside b 1 bs → ¬ Blocks.Inside b 1 bs'

axiom Blocks.Inside.add_ofNat {w : Nat} {bs : List (BitVec w × Nat)} {addr : BitVec w}
    {n i : Nat} (hin : Blocks.Inside addr n bs) (hi : i < n) :
    Blocks.Inside (addr + BitVec.ofNat w i) 1 bs

axiom Mapped.loadInt_isSome {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w}
    {addr : BitVec w} {n : Nat} (h : Mapped bs m) (hin : Blocks.Inside addr n bs) :
    (m.loadInt addr n).isSome = true

axiom Mapped.storeInt {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w} (h : Mapped bs m)
    (a : BitVec w) (n : Nat) (v : Int) : Mapped bs (m.storeInt a n v)

axiom Blocks.Inside.of_singleton {w : Nat} {b x : BitVec w} {n : Nat} {bs : List (BitVec w × Nat)}
    (hb : Blocks.Inside b 1 [(x, n)]) (hx : Blocks.Inside x n bs) : Blocks.Inside b 1 bs

axiom Blocks.Disjoint.of_inside' {w : Nat} {x d : BitVec w} {n k : Nat}
    {bs₁ bs₂ : List (BitVec w × Nat)} (hd : Blocks.Disjoint bs₁ bs₂) (hx : Blocks.Inside x n bs₂)
    (hy : Blocks.Inside d k bs₁) : Blocks.Disjoint [(x, n)] [(d, k)]

axiom loadInt_storeInt_of_disjoint {w : Nat} {m : Mem w} {a x : BitVec w} {n k : Nat}
    (hd : Blocks.Disjoint [(x, k)] [(a, n)]) (v : Int) :
    (m.storeInt a n v).loadInt x k = m.loadInt x k

axiom Blocks.Disjoint.of_sub {w : Nat} {x a : BitVec w} {k n : Nat}
    (h₁ : n ≤ (x - a).toNat) (h₂ : k ≤ (a - x).toNat) : Blocks.Disjoint [(x, k)] [(a, n)]

def Blocks.decInside {w : Nat} (a : BitVec w) (n : Nat) :
    (bs : List (BitVec w × Nat)) → Decidable (Blocks.Inside a n bs)
  | [] => isFalse id
  | (_, _) :: bs => @instDecidableOr _ _ (Nat.decLe _ _) (Blocks.decInside a n bs)

instance {w : Nat} {a : BitVec w} {n : Nat} {bs : List (BitVec w × Nat)} :
    Decidable (Blocks.Inside a n bs) :=
  Blocks.decInside a n bs

opaque restrict {w : Nat} (y : Mem w) (bs : List (BitVec w × Nat)) : Mem w

axiom get?_restrict {w : Nat} (y : Mem w) (bs : List (BitVec w × Nat)) (b : BitVec w) :
    (y.restrict bs).get? b = if Blocks.Inside b 1 bs then y.get? b else none

axiom get?_storeInt {w : Nat} (m : Mem w) (a b : BitVec w) (n : Nat) (v : Int) :
    (m.storeInt a n v).get? b = ((Int.toBytes n v).At a)[b]?.or (m.get? b)

axiom loadInt_restrict_of_inside {w : Nat} {y : Mem w} {bs : List (BitVec w × Nat)} {a : BitVec w}
    {n : Nat} (h : Blocks.Inside a n bs) : (y.restrict bs).loadInt a n = y.loadInt a n

grind_pattern Blocks.Inside.base => Blocks.Inside a n ((a, len) :: bs)
grind_pattern Blocks.Inside.base_add => Blocks.Inside (a + x) n ((a, len) :: bs)
grind_pattern Mapped.loadInt_isSome => Mapped bs m, Mem.loadInt m addr n
grind_pattern Mapped.storeInt => Mapped bs m, Mem.storeInt m a n v
grind_pattern loadInt_storeInt_of_disjoint => Mem.loadInt (Mem.storeInt m a n v) x k
grind_pattern loadInt_restrict_of_inside => Mem.loadInt (restrict y bs) a n

end Mem
