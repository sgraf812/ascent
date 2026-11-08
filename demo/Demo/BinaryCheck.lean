import Demo.Binary

/-!
# Checking that bytes assemble a program

`Binary.check p sizes b` walks the program `p`, the size list `sizes` and the bytes of `b` together
in one pass. At each instruction it decodes the bytes at the current address and compares the
result with the instruction, its size and its jump target. A jump target is the address of a label,
found in the list of label addresses that the same kind of pass collects; the comparison tests the
address first, so label names are compared only at the matching address. `Host.ofCheck` builds the
host that lays out `p` with `sizes` from `Binary.base`, and `Binary.assembles_of_check` proves
`Binary.Assembles p b` at that host. A concrete instance of both needs only the evaluation of
`check p sizes b`.
-/

namespace Ascent.Kraken

namespace Binary

def labelAddrs : Int64 → Program → List Nat → List (Label × Int64)
  | a, .label l :: ds, s :: ss => (l, a) :: labelAddrs (a + .ofNat s) ds ss
  | a, _ :: ds, s :: ss => labelAddrs (a + .ofNat s) ds ss
  | _, _, _ => []

def off (a : Int64) : Nat := (a - base).toBitVec.toNat

inductive LTree where
  | leaf
  | node (l : LTree) (k : Nat) (v : Label) (r : LTree)

def LTree.find? : LTree → Nat → Option Label
  | .leaf, _ => none
  | .node l k v r, x => bif Nat.blt x k then l.find? x else bif Nat.beq x k then some v else r.find? x

def LTree.build : Nat → List (Nat × Label) → LTree
  | 0, _ => .leaf
  | f + 1, xs =>
    match xs.splitAt (xs.length / 2) with
    | (ls, (k, v) :: rs) => .node (build f ls) k v (build f rs)
    | _ => .leaf

def LTree.Has : LTree → Nat → Label → Prop
  | .leaf, _, _ => False
  | .node l k w r, x, v => (x = k ∧ v = w) ∨ l.Has x v ∨ r.Has x v

def labelTree (lbls : List (Label × Int64)) : LTree :=
  .build lbls.length (lbls.map fun x => (off x.2, x.1))

def targetOK (t : LTree) : Option Label → Option Int64 → Bool
  | none, none => true
  | some l, some a => (t.find? (off a)).any (· == l)
  | _, _ => false

def walkOK (t : LTree) : Int64 → List UInt8 → Program → List Nat → Bool
  | a, bs, .label _ :: ds, s :: ss => s == 0 && walkOK t (a + .ofNat s) bs ds ss
  | a, bs, .instr i :: ds, s :: ss =>
    (match decode a bs with
      | some (j, n, u) => j == i.eraseLabel && n == s && Nat.blt 0 s && targetOK t i.target? u
      | none => false) && walkOK t (a + .ofNat s) (bs.drop s) ds ss
  | _, _, [], [] => true
  | _, _, _, _ => false

def jumpTargets : Int64 → List UInt8 → Program → List Nat → List Int64
  | a, bs, .instr _ :: ds, s :: ss =>
    (match decode a bs with
      | some (_, _, some t) => [t]
      | _ => []) ++ jumpTargets (a + .ofNat s) (bs.drop s) ds ss
  | a, bs, _ :: ds, s :: ss => jumpTargets (a + .ofNat s) bs ds ss
  | _, _, _, _ => []

def bitsOf (size : Nat) : List Int64 → Nat
  | [] => 0
  | t :: ts => bif Nat.blt (off t) size then bitsOf size ts ||| 1 <<< off t else bitsOf size ts

def hashLabel (l : Label) : Nat :=
  l.toUTF8.data.toList.foldl (fun h x => (h * 257 + x.toNat) % 1048573) 0

def distinctBits : Nat → List Nat → Bool
  | _, [] => true
  | m, h :: hs => !m.testBit h && distinctBits (m ||| 1 <<< h) hs

def nodupB : List Label → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

def labelsNodup (ls : List Label) : Bool :=
  distinctBits 0 (ls.map hashLabel) || nodupB ls

def check (p : Program) (sizes : List Nat) (b : ByteArray) : Bool :=
  let lbls := labelAddrs base p sizes
  let jts := bitsOf b.size (jumpTargets base b.data.toList p sizes)
  walkOK (labelTree lbls) base b.data.toList p sizes && sizes.sum == b.size &&
    Nat.blt (base.toBitVec.toNat + b.size) (2 ^ 64 - 1) && labelsNodup p.labels &&
    lbls.all fun x => jts.testBit (off x.2)

/-! ## Soundness of the parts -/

theorem LTree.find?_sound {t : LTree} {x : Nat} {v : Label} (h : t.find? x = some v) :
    t.Has x v := by
  induction t with
  | leaf => simp [LTree.find?] at h
  | node l k w r ihl ihr =>
    simp only [LTree.find?] at h
    cases hlt : Nat.blt x k <;> simp only [hlt, Bool.cond_true, Bool.cond_false] at h
    · cases heq : Nat.beq x k <;> simp only [heq, Bool.cond_true, Bool.cond_false] at h
      · exact Or.inr (Or.inr (ihr h))
      · exact Or.inl ⟨Nat.eq_of_beq_eq_true heq, (Option.some.inj h).symm⟩
    · exact Or.inr (Or.inl (ihl h))

theorem LTree.has_build {f : Nat} {xs : List (Nat × Label)} {x : Nat} {v : Label}
    (h : (LTree.build f xs).Has x v) : (x, v) ∈ xs := by
  induction f generalizing xs with
  | zero => simp [LTree.build, LTree.Has] at h
  | succ f ih =>
    simp only [LTree.build] at h
    split at h
    · rename_i ls k w rs hsplit
      rw [List.splitAt_eq] at hsplit
      obtain ⟨hl, hr⟩ := Prod.mk.inj hsplit
      rcases h with ⟨rfl, rfl⟩ | h | h
      · exact List.mem_of_mem_drop (hr ▸ List.mem_cons_self)
      · exact List.mem_of_mem_take (hl ▸ ih h)
      · exact List.mem_of_mem_drop (hr ▸ List.mem_cons_of_mem _ (ih h))
    · simp [LTree.Has] at h

theorem off_inj {a b : Int64} (h : off a = off b) : a = b := by
  have h' : (a - base).toBitVec = (b - base).toBitVec := BitVec.eq_of_toNat_eq h
  have := Int64.toBitVec_inj.mp h'
  simpa using congrArg (· + base) this

theorem off_base_add {c : Nat} (hc : c < 2 ^ 64) : off (base + .ofNat c) = c := by
  have : base + Int64.ofNat c - base = Int64.ofNat c := by
    rw [Int64.add_comm, Int64.add_sub_cancel]
  rw [off, this, Kraken.Int64.toBitVec_ofNat_grind]
  show (BitVec.ofNat 64 c).toNat = c
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

theorem mem_of_testBit_bitsOf {size i : Nat} {ts : List Int64} (h : (bitsOf size ts).testBit i = true) :
    ∃ t ∈ ts, off t = i := by
  induction ts with
  | nil => simp [bitsOf] at h
  | cons t ts ih =>
    simp only [bitsOf] at h
    cases hb : Nat.blt (off t) size <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
    · obtain ⟨u, hu, rfl⟩ := ih h
      exact ⟨u, List.mem_cons_of_mem _ hu, rfl⟩
    · rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · obtain ⟨u, hu, rfl⟩ := ih h
        exact ⟨u, List.mem_cons_of_mem _ hu, rfl⟩
      · exact ⟨t, List.mem_cons_self, (of_decide_eq_true h)⟩

theorem nodup_of_distinctBits {m : Nat} {hs : List Nat} (h : distinctBits m hs = true) :
    hs.Nodup ∧ ∀ x ∈ hs, m.testBit x = false := by
  induction hs generalizing m with
  | nil => simp
  | cons x hs ih =>
    simp only [distinctBits, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hnd, hall⟩ := ih h.2
    refine ⟨List.nodup_cons.mpr ⟨fun hx => ?_, hnd⟩, ?_⟩
    · have := hall x hx
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow] at this
      simp at this
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h.1
      · have := hall y hy
        rw [Nat.testBit_or] at this
        exact (Bool.or_eq_false_iff.mp this).1

theorem nodup_of_map {f : Label → Nat} {ls : List Label} (h : (ls.map f).Nodup) : ls.Nodup := by
  induction ls with
  | nil => simp
  | cons x ls ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h ⊢
    exact ⟨fun hx => h.1 ⟨x, hx, rfl⟩, ih h.2⟩

theorem nodup_of_nodupB {ls : List Label} (h : nodupB ls = true) : ls.Nodup := by
  induction ls with
  | nil => simp
  | cons x ls ih =>
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact List.nodup_cons.mpr ⟨by simpa using h.1, ih h.2⟩

theorem nodup_of_labelsNodup {ls : List Label} (h : labelsNodup ls = true) : ls.Nodup := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact nodup_of_map (nodup_of_distinctBits h).1
  · exact nodup_of_nodupB h


/-! ## The walk -/

def DirOK (t : LTree) (a : Int64) (bs : List UInt8) : Directive → Nat → Prop
  | .label _, s => s = 0
  | .instr i, s => 0 < s ∧ ∃ u, decode a bs = some (i.eraseLabel, s, u) ∧ targetOK t i.target? u = true
  | .byteArray _, _ => False

theorem add_ofNat_zero (a : Int64) : a + .ofNat 0 = a := by
  rw [show Int64.ofNat 0 = 0 from rfl, Int64.add_zero]

theorem add_ofNat_add (a : Int64) (m n : Nat) : a + .ofNat (m + n) = a + .ofNat m + .ofNat n := by
  rw [Int64.ofNat_add, Int64.add_assoc]

theorem walkOK_length {t : LTree} {a : Int64} {bs : List UInt8} {ds : Program} {ss : List Nat}
    (h : walkOK t a bs ds ss = true) : ds.length = ss.length := by
  induction ds generalizing a bs ss with
  | nil => cases ss <;> simp_all [walkOK]
  | cons d ds ih =>
    cases ss with
    | nil => cases d <;> simp [walkOK] at h
    | cons s ss =>
      cases d <;> simp only [walkOK, Bool.and_eq_true] at h
      · simp [ih h.2]
      · simp [ih h.2]
      · simp at h

theorem walkOK_get {t : LTree} {a : Int64} {bs : List UInt8} {ds : Program} {ss : List Nat}
    (h : walkOK t a bs ds ss = true) {k : Nat} {d : Directive} {s : Nat} (hd : ds[k]? = some d)
    (hs : ss[k]? = some s) :
    DirOK t (a + .ofNat (ss.take k).sum) (bs.drop (ss.take k).sum) d s := by
  induction ds generalizing a bs ss k with
  | nil => simp at hd
  | cons d' ds ih =>
    cases ss with
    | nil => simp at hs
    | cons s' ss =>
      cases d' with
      | label l =>
        simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hd hs
          subst hd hs
          rfl
        | succ k =>
          simp only [List.getElem?_cons_succ] at hd hs
          have := ih h hd hs
          simpa [List.take_succ_cons, List.sum_cons, add_ofNat_zero] using this
      | instr i =>
        simp only [walkOK, Bool.and_eq_true] at h
        obtain ⟨hi, h⟩ := h
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hd hs
          subst hd hs
          simp only [List.take_zero, List.sum_nil, add_ofNat_zero, List.drop_zero]
          split at hi
          · rename_i j n u hdec
            simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hi
            obtain ⟨⟨⟨rfl, rfl⟩, hpos⟩, ht⟩ := hi
            exact ⟨hpos, u, hdec, ht⟩
          · simp at hi
        | succ k =>
          simp only [List.getElem?_cons_succ] at hd hs
          have := ih h hd hs
          rw [List.drop_drop] at this
          simpa only [List.take_succ_cons, List.sum_cons, add_ofNat_add] using this
      | byteArray _ => simp [walkOK] at h


/-! ## Labels -/

theorem labelAddrs_fst {a : Int64} {ds : Program} {ss : List Nat} (h : ds.length = ss.length) :
    (labelAddrs a ds ss).map Prod.fst = Program.labels ds := by
  induction ds generalizing a ss with
  | nil => cases ss <;> simp [labelAddrs]
  | cons d ds ih =>
    cases ss with
    | nil => simp at h
    | cons s ss =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      cases d <;> simp [labelAddrs, Program.labels, Directive.label?, ih h, List.filterMap_cons] <;>
        rfl

theorem findSome_withAddresses (l : Label) {a : Int64} {ds : Program} {ss : List Nat}
    (h : ds.length = ss.length) :
    (Kraken.Executable.withAddresses
        ({startAddr := a, program := List.zipWith (fun d s => ⟨d, s⟩) ds ss} : Executable)).findSome?
      (fun x => if x.directive = .label l then some x.addr else none) =
    (labelAddrs a ds ss).findSome? (fun x => if x.1 = l then some x.2 else none) := by
  induction ds generalizing a ss with
  | nil => cases ss <;> simp [labelAddrs, Kraken.Executable.withAddresses.eq_1]
  | cons d ds ih =>
    cases ss with
    | nil => simp at h
    | cons s ss =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.zipWith_cons_cons, Kraken.Executable.withAddresses.eq_2]
      cases d with
      | label l' =>
        by_cases hl : l' = l
        · subst hl; simp [labelAddrs]
        · simp [labelAddrs, hl, ih h]
      | instr i => simp [labelAddrs, ih h]
      | byteArray x => simp [labelAddrs, ih h]

theorem findSome_eq_of_mem {xs : List (Label × Int64)} (hnd : (xs.map Prod.fst).Nodup) {l : Label}
    {t : Int64} (hm : (l, t) ∈ xs) :
    xs.findSome? (fun x => if x.1 = l then some x.2 else none) = some t := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    · have hx : x.1 ≠ l := fun hx => hnd.1 ⟨(l, t), hm, hx.symm⟩
      simp [hx, ih hnd.2 hm]

theorem mem_of_targetOK {lbls : List (Label × Int64)} {l : Label} {a : Int64}
    (h : targetOK (labelTree lbls) (some l) (some a) = true) : (l, a) ∈ lbls := by
  simp only [targetOK, Option.any_eq_true, beq_iff_eq] at h
  obtain ⟨l', hf, rfl⟩ := h
  have := LTree.has_build (LTree.find?_sound hf)
  obtain ⟨x, hx, hx'⟩ := List.mem_map.mp this
  obtain ⟨hoff, rfl⟩ := Prod.mk.inj hx'
  rw [← off_inj hoff]
  exact hx


/-! ## Layout and jump targets -/

@[instance_reducible] def layoutOf (sizes : List Nat) : Layout where
  start := base
  size i := sizes[i]?.getD 0

theorem apply_layoutOf {p : Program} {sizes : List Nat} (h : p.length = sizes.length) :
    (layoutOf sizes).apply p = {startAddr := base, program := List.zipWith (fun d s => ⟨d, s⟩) p sizes} := by
  simp only [Kraken.Layout.apply]
  congr 1
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_mapIdx, List.getElem?_zipWith]
  rcases hp : p[i]? with _ | d
  · rfl
  · have hi : i < sizes.length := h ▸ (List.getElem?_eq_some_iff.mp hp).1
    simp only [List.getElem?_eq_getElem hi, Option.map_some]
    show some ({directive := d, size := sizes[i]?.getD 0} : Kraken.Sized Directive) = _
    simp [List.getElem?_eq_getElem hi]

theorem map_size_zipWith {p : Program} {sizes : List Nat} (h : p.length = sizes.length) :
    (List.zipWith (fun d s => (⟨d, s⟩ : Kraken.Sized Directive)) p sizes).map (·.size) = sizes := by
  induction p generalizing sizes with
  | nil => cases sizes <;> simp_all
  | cons d p ih =>
    cases sizes with
    | nil => simp at h
    | cons s sizes => simp_all

theorem addrOf_layoutOf {p : Program} {sizes : List Nat} (h : p.length = sizes.length) (k : Nat) :
    ((layoutOf sizes).apply p).addrOf k = base + .ofNat (sizes.take k).sum := by
  rw [apply_layoutOf h, Kraken.Executable.addrOf, Kraken.Executable.sizeBefore]
  show base + _ = _
  rw [List.map_take, map_size_zipWith h]

theorem fetch_eq (b : ByteArray) (a : Int64) : fetch b a = b.data.toList.drop (off a) := rfl

theorem length_toList (b : ByteArray) : b.data.toList.length = b.size := Array.length_toList

theorem mem_jumpTargets {t : LTree} {a : Int64} {bs : List UInt8} {ds : Program} {ss : List Nat}
    (h : walkOK t a bs ds ss = true) {x : Int64} (hx : x ∈ jumpTargets a bs ds ss) :
    ∃ l, targetOK t (some l) (some x) = true := by
  induction ds generalizing a bs ss with
  | nil => cases ss <;> simp [jumpTargets] at hx
  | cons d ds ih =>
    cases ss with
    | nil => cases d <;> simp [jumpTargets] at hx
    | cons s ss =>
      cases d with
      | label l =>
        simp only [walkOK, Bool.and_eq_true] at h
        exact ih h.2 hx
      | instr i =>
        simp only [walkOK, Bool.and_eq_true] at h
        simp only [jumpTargets, List.mem_append] at hx
        rcases hx with hx | hx
        · obtain ⟨hi, -⟩ := h
          split at hi
          · rename_i j n u hdec
            simp only [hdec] at hx
            cases u with
            | none => simp at hx
            | some u =>
              simp only [List.mem_singleton] at hx
              subst hx
              simp only [Bool.and_eq_true] at hi
              cases hl : i.target? with
              | none => simp [hl, targetOK] at hi
              | some l => exact ⟨l, hl ▸ hi.2⟩
          · simp at hi
        · exact ih h.2 hx
      | byteArray _ => simp [walkOK] at h

theorem targetsFrom_eq {b : ByteArray} {t : LTree} {a : Int64} {bs : List UInt8} {ds : Program}
    {ss : List Nat} {c : Nat} (h : walkOK t a bs ds ss = true) (ha : a = base + .ofNat c)
    (hbs : bs = b.data.toList.drop c) (hsum : c + ss.sum = b.size) (hb : b.size < 2 ^ 64)
    {fuel : Nat} (hf : bs.length ≤ fuel) : targetsFrom b fuel a = jumpTargets a bs ds ss := by
  have hfetch : fetch b a = bs := by
    rw [fetch_eq, hbs, ha, off_base_add (by omega)]
  induction ds generalizing a bs ss c fuel with
  | nil =>
    cases ss with
    | cons _ _ => simp [walkOK] at h
    | nil =>
      have : bs = [] := by
        rw [hbs]; apply List.drop_eq_nil_of_le; rw [length_toList]; simp at hsum; omega
      cases fuel <;> simp [targetsFrom, jumpTargets, decodeAt, hfetch, this, decode]
  | cons d ds ih =>
    cases ss with
    | nil => cases d <;> simp [walkOK] at h
    | cons s ss =>
      cases d with
      | label l =>
        simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        rw [jumpTargets, ← ih h (by rw [add_ofNat_zero, ha]) hbs (by simpa using hsum) hf
            (by rw [add_ofNat_zero, hfetch]), add_ofNat_zero]
        simp
      | instr i =>
        simp only [walkOK, Bool.and_eq_true] at h
        obtain ⟨hi, h⟩ := h
        split at hi
        · rename_i j n u hdec
          simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hi
          obtain ⟨⟨⟨rfl, rfl⟩, hpos⟩, -⟩ := hi
          have hlen : bs.length = b.size - c := by rw [hbs, List.length_drop, length_toList]
          simp only [List.sum_cons] at hsum
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          have := ih h (c := c + n) (by rw [ha, add_ofNat_add]) (by rw [hbs, List.drop_drop])
            (by omega) (fuel := f) (by rw [List.length_drop]; omega)
            (by rw [fetch_eq, ha, ← add_ofNat_add, off_base_add (by omega), hbs, List.drop_drop])
          rw [targetsFrom, decodeAt, hfetch, hdec, jumpTargets, hdec]
          simp only [this]
          cases u <;> rfl
        · simp at hi
      | byteArray _ => simp [walkOK] at h


/-! ## The host of a passing check -/

theorem check_parts {p : Program} {sizes : List Nat} {b : ByteArray} (h : check p sizes b = true) :
    walkOK (labelTree (labelAddrs base p sizes)) base b.data.toList p sizes = true ∧
      sizes.sum = b.size ∧ base.toBitVec.toNat + b.size < 2 ^ 64 - 1 ∧ p.labels.Nodup ∧
      ∀ x ∈ labelAddrs base p sizes,
        (bitsOf b.size (jumpTargets base b.data.toList p sizes)).testBit (off x.2) = true := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, nodup_of_labelsNodup h.1.2, h.2⟩

theorem toNat_base_add {x : Nat} (hx : base.toBitVec.toNat + x < 2 ^ 64) :
    (base + .ofNat x).toBitVec.toNat = base.toBitVec.toNat + x := by
  rw [Int64.toBitVec_add, Kraken.Int64.toBitVec_ofNat_grind, BitVec.toNat_add]
  show (base.toBitVec.toNat + (BitVec.ofNat 64 x).toNat) % 2 ^ 64 = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x) (by omega), Nat.mod_eq_of_lt hx]

theorem sum_take_le (sizes : List Nat) (k : Nat) : (sizes.take k).sum ≤ sizes.sum := by
  induction sizes generalizing k with
  | nil => simp
  | cons s sizes ih => cases k <;> simp [ih]

theorem getElem?_sizes {p : Program} {sizes : List Nat} (h : p.length = sizes.length) {i : Nat}
    {d : Directive} (hd : p[i]? = some d) : sizes[i]? = some (sizes[i]?.getD 0) := by
  have : i < sizes.length := h ▸ (List.getElem?_eq_some_iff.mp hd).1
  simp [List.getElem?_eq_getElem this]

end Binary

open Binary in
@[instance_reducible] def Host.ofCheck (p : Program) (sizes : List Nat) (b : ByteArray)
    (h : check p sizes b = true) : Host where
  prog := p
  layout := layoutOf sizes
  labels_nodup := (check_parts h).2.2.2.1
  label_size i l hi := by
    have hw := (check_parts h).1
    exact walkOK_get hw hi (getElem?_sizes (walkOK_length hw) hi)
  instr_size_pos i ins hi _ := by
    have hw := (check_parts h).1
    exact (walkOK_get hw hi (getElem?_sizes (walkOK_length hw) hi)).1
  instr_addr_ne i ins _ := by
    obtain ⟨hw, hsum, hb, -⟩ := check_parts h
    rw [addrOf_layoutOf (walkOK_length hw)]
    intro he
    have := congrArg (fun x : Int64 => x.toBitVec.toNat) he
    have hle := sum_take_le sizes i
    rw [toNat_base_add (by omega)] at this
    have : (-1 : Int64).toBitVec.toNat = 2 ^ 64 - 1 := rfl
    omega
  zero_inert i d hi hz := by
    have hw := (check_parts h).1
    have hd := walkOK_get hw hi (getElem?_sizes (walkOK_length hw) hi)
    have hz' : sizes[i]?.getD 0 = 0 := hz
    rw [hz'] at hd
    match d, hd with
    | .label l, _ => exact @Binary.label_inert l
    | .instr _, hd => exact (Nat.lt_irrefl 0 hd.1).elim
    | .byteArray _, hd => exact hd.elim
  addr_determines_offset j k he := by
    obtain ⟨hw, hsum, hb, -⟩ := check_parts h
    have hl := walkOK_length hw
    rw [addrOf_layoutOf hl, addrOf_layoutOf hl] at he
    have := congrArg (fun x : Int64 => x.toBitVec.toNat) he
    have hj := sum_take_le sizes j
    have hk := sum_take_le sizes k
    rw [toNat_base_add (by omega), toNat_base_add (by omega)] at this
    simp only [Kraken.Executable.sizeBefore, apply_layoutOf hl]
    rw [List.map_take, List.map_take, map_size_zipWith hl]
    omega

namespace Binary


theorem exe_ofCheck {p : Program} {sizes : List Nat} {b : ByteArray} (h : check p sizes b = true) :
    @Host.exe (Host.ofCheck p sizes b h) = (layoutOf sizes).apply p := rfl

theorem label_ofCheck {p : Program} {sizes : List Nat} {b : ByteArray} (h : check p sizes b = true)
    {l : Label} {a : Int64} (hm : (l, a) ∈ labelAddrs base p sizes) :
    (Executable.labels (@Host.exe (Host.ofCheck p sizes b h))).label l = a := by
  obtain ⟨hw, -, -, hnd, -⟩ := check_parts h
  have hl := walkOK_length hw
  show ((Kraken.Executable.withAddresses (@Host.exe (Host.ofCheck p sizes b h))).findSome?
    (fun x => if x.directive = .label l then some x.addr else none)).getD (-1) = a
  rw [exe_ofCheck, apply_layoutOf hl, findSome_withAddresses l hl,
    findSome_eq_of_mem (by rw [labelAddrs_fst hl]; exact hnd) hm]
  rfl

theorem targets_eq_jumpTargets {p : Program} {sizes : List Nat} {b : ByteArray}
    (h : check p sizes b = true) : targets b = jumpTargets base b.data.toList p sizes := by
  obtain ⟨hw, hsum, hb, -⟩ := check_parts h
  exact targetsFrom_eq hw (c := 0) (add_ofNat_zero base).symm (List.drop_zero).symm
    (by omega) (by omega) (Nat.le_of_eq (length_toList b))

theorem assembles_of_check {p : Program} {sizes : List Nat} {b : ByteArray}
    (h : check p sizes b = true) : @Assembles (Host.ofCheck p sizes b h) p b := by
  obtain ⟨hw, hsum, hb, hnd, hcov⟩ := check_parts h
  have hl := walkOK_length hw
  have haddr (k : Nat) : @Host.addrOf (Host.ofCheck p sizes b h) k = base + .ofNat (sizes.take k).sum :=
    addrOf_layoutOf hl k
  refine @Assembles.mk (Host.ofCheck p sizes b h) p b rfl ?_ ?_ ?_ ?_
  · rw [haddr]; exact add_ofNat_zero base
  · rw [haddr, List.take_of_length_le (Nat.le_of_eq hl.symm), hsum]
  · intro k c hc hz
    rw [exe_ofCheck, apply_layoutOf hl, List.getElem?_zipWith] at hc
    rcases hd : p[k]? with _ | d <;> rcases hs : sizes[k]? with _ | s <;> simp only [hd, hs] at hc
    · cases hc
    · cases hc
    · cases hc
    simp only [Option.some.injEq] at hc
    subst hc
    have hk := walkOK_get hw hd hs
    have hle := sum_take_le sizes k
    rw [haddr, fetch_eq, off_base_add (by omega)]
    match d, hk with
    | .label _, hk => exact absurd hk (Nat.ne_of_gt hz)
    | .byteArray _, hk => exact hk.elim
    | .instr i, ⟨_, u, hdec, ht⟩ =>
      refine ⟨i, rfl, ?_⟩
      rw [hdec]
      cases hi : i.target? with
      | none => cases u <;> simp_all [targetOK]
      | some l =>
        cases u with
        | none => simp [hi, targetOK] at ht
        | some u =>
          rw [hi] at ht
          simp only [Option.map_some]
          rw [label_ofCheck h (mem_of_targetOK ht)]
  · intro a
    rw [targets_eq_jumpTargets h]
    constructor
    · intro ha
      obtain ⟨l, hl'⟩ := mem_jumpTargets hw ha
      have hm := mem_of_targetOK hl'
      refine ⟨l, ?_, label_ofCheck h hm⟩
      rw [← labelAddrs_fst hl]
      exact List.mem_map.mpr ⟨(l, a), hm, rfl⟩
    · rintro ⟨l, hlm, rfl⟩
      rw [← labelAddrs_fst hl] at hlm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hlm
      have hlab := label_ofCheck h (l := x.1) (a := x.2) hx
      show (Executable.labels (@Host.exe (Host.ofCheck p sizes b h))).label x.1 ∈ _
      rw [hlab]
      obtain ⟨t, ht, hoff⟩ := mem_of_testBit_bitsOf (hcov x hx)
      rw [← off_inj hoff]
      exact ht


end Binary

end Ascent.Kraken
