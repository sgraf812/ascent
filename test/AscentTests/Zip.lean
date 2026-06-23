import AscentTests.Loop

/-!
# L1 denotational semantics of `zip_with_add`

The initial denotation of

```c
size_t zip_with_add(const int *a, size_t len_a, const int *b, size_t len_b, int *out) {
    size_t n = len_a < len_b ? len_a : len_b;
    for (size_t i = 0; i < n; i++) out[i] = a[i] + b[i];
    return n;
}
```

Locals live in the state as an untyped map `Ident → Option Value` (shape borrowed from the
CLight densem; nothing else copied). Every memory access is preceded by a `c_guard`; a
missing/wrong-typed local projection is itself undefined behaviour. `int` is `Int32` with
wrapping `+` and no overflow guard. No `ExceptT`: the single `return n` is in tail position.
-/

open Std.Internal.Do Lean.Order Ascent

namespace Zip

abbrev Addr := Nat
abbrev I    := Int32                          -- C `int`

structure Heap where
  data  : Addr → I
  valid : Addr → Bool                         -- heap type description: where c_guard succeeds

abbrev Ident := String

inductive Value                               -- minimal untyped value domain (cf. CLight's CVal)
  | int  (v : I)
  | ptr  (a : Addr)
  | size (n : USize)

abbrev Locals := Ident → Option Value

structure State where
  locals : Locals
  heap   : Heap

abbrev M := StateT State UB                    -- state (locals + heap) + UB; no ExceptT

/-- Memory load (well-defined only after `c_guard`). -/
def load (p : Addr) : M I := fun s => some (s.heap.data p, s)
/-- Memory store. -/
def store (p : Addr) (v : I) : M Unit :=
  fun s => some (⟨⟩, { s with heap.data := fun a => if a = p then v else s.heap.data a })
/-- The parser's `c_guard`: UB unless `p` is a valid pointer. -/
def cguard (p : Addr) : M Unit := fun s => if s.heap.valid p then some (⟨⟩, s) else UB.fail

/-- Read a `size_t` local; UB if missing or wrong type. -/
def getSize (x : Ident) : M USize := fun s => match s.locals x with | some (.size n) => some (n, s) | _ => UB.fail
/-- Read a pointer local; UB if missing or wrong type. -/
def getPtr (x : Ident) : M Addr := fun s => match s.locals x with | some (.ptr a) => some (a, s) | _ => UB.fail
/-- Write a `size_t` local. -/
def setSize (x : Ident) (n : USize) : M Unit :=
  fun s => some (⟨⟩, { s with locals := fun y => if y = x then some (.size n) else s.locals y })

/-- L1 denotation of `zip_with_add`. -/
def den : M USize := do
  let la ← getSize "len_a"
  let lb ← getSize "len_b"
  setSize "n" (if la < lb then la else lb)              -- size_t n = len_a < len_b ? len_a : len_b;
  setSize "i" 0
  whileLoop                                              -- for (i = 0; i < n; i++)
    (fun s => match s.locals "i", s.locals "n" with
      | some (.size i), some (.size n) => decide (i < n)
      | _, _ => false)
    (do
      let i   ← getSize "i"
      let a   ← getPtr "a"
      let b   ← getPtr "b"
      let out ← getPtr "out"
      cguard (a + i.toNat);   let x ← load (a + i.toNat)
      cguard (b + i.toNat);   let y ← load (b + i.toNat)
      cguard (out + i.toNat); store (out + i.toNat) (x + y)     -- Int32 wrapping +, no overflow guard
      setSize "i" (i + 1))
  getSize "n"                                            -- return n;

end Zip
