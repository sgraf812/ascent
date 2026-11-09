import Demo.ZipStruct

/-!
# Register lifting

A program over `MachineData` refines a program over the data memory alone, under
`ofStateRepr MachineData.dmem`. A register read in the concrete program becomes a value of the
abstract program: the hypothesis `PureRefinement (t.regs.get64 r) x True Eq` relates the register
`r` of the state `t` to the abstract value `x`, and the `@[ascend_pure]` rules below abstract a
value computed from registers to the same computation on the abstract values. A step that writes a
register binds the abstract value of the written value to a variable of the abstract program.

The step rules know no instruction. They match the three writes of `Demo.L1`: a load into a
register `loadReg n` becomes `load n` and binds the loaded word, a store `storeWord n` becomes
`store n`, a register write `setReg64` leaves the memory unchanged and adds no abstract step, and an
exit `exitIf g f l` whose guard `g` reads a mapped word becomes `assume g'; throw l` with the guard
`g'` restated over the data memory.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Kraken

/-! ## Memory steps -/

/-- The `n`-byte word at `a`, zero-extended to 64 bits, undefined behaviour when the cell is not
mapped. -/
noncomputable def load (n : Nat) (a : BitVec 64) : BlockM DataMem (BitVec 64) := fun m =>
  UB.assume ((Mem.loadInt m a n).isSome = true) >>= fun _ =>
    pure (.ok (BitVec.ofInt 64 ((Mem.loadInt m a n).get! % 2 ^ (8 * n))), m)

/-- Store the low `n` bytes of `v` at `a`, undefined behaviour unless the cell is mapped and apart
from the return slot at `rsp`. -/
noncomputable def store (n : Nat) (rsp a v : BitVec 64) : BlockM DataMem Unit :=
  modifyIf (fun m => (Mem.loadInt m a n).isSome = true ∧ Mem.Blocks.Disjoint [(rsp, 8)] [(a, n)])
    fun m => Mem.storeInt m a n v.toInt

theorem ofInt_emod_two_pow (n : Nat) (x : Int) : BitVec.ofInt n (x % 2 ^ n) = BitVec.ofInt n x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, Int.natCast_pow, Int.cast_ofNat_Int, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]

section
variable (Q : BitVec 64 → DataMem → Prop) (Qu : Unit → DataMem → Prop)
  (E : (CfgLabel → DataMem → Prop) × EStack⟨⟩) (m : DataMem)

theorem wp_load (n : Nat) (a : BitVec 64) :
    wp (load n a) Q E m
      = ((Mem.loadInt m a n).isSome = true
          ∧ Q (BitVec.ofInt 64 ((Mem.loadInt m a n).get! % 2 ^ (8 * n))) m) := by
  rw [wp_BlockM_eq, show (load n a).run.run m = load n a m from rfl, load]
  by_cases h : (Mem.loadInt m a n).isSome = true
  · rw [UB.assume_bind_of_pos h]
    simp only [h, true_and]
    rfl
  · rw [UB.assume_bind_of_neg h, UB.fail_eq]
    simp only [Bool.not_eq_true] at h
    simp [h]

theorem wp_store (n : Nat) (rsp a v : BitVec 64) :
    wp (store n rsp a v) Qu E m
      = (((Mem.loadInt m a n).isSome = true ∧ Mem.Blocks.Disjoint [(rsp, 8)] [(a, n)])
          ∧ Qu () (Mem.storeInt m a n v.toInt)) := wp_modifyIf _ _ _ _ _

theorem wp_assume_throw {α : Type} {Qα : α → DataMem → Prop} (g : DataMem → Prop) (l : CfgLabel) :
    wp (do StateT.assume g; throw l : BlockM DataMem α) Qα E m = (g m ∧ E.1 l m) := by
  rw [WPMonadExact.wp_bind_eq, ExceptT.wp_monadLift_StateT_UB, StateT.wp_assume_eq, wp_throw_block]

end

/-- `c ≐ x`: the concrete value `c` abstracts to the abstract value `x`. -/
scoped notation:50 c:51 " ≐ " x:51 => PureRefinement c x True Eq

/-! ## Values -/

/-- `RegsRel rs t`: each register `r` of `rs` holds its abstract value `v` in the state `t`. -/
abbrev RegsRel : List (Reg64 × BitVec 64) → MachineData → Prop
  | [], _ => True
  | (r, v) :: rs, t => t.regs.get64 r ≐ v ∧ RegsRel rs t

attribute [vcgen_simp] RegsRel

section
variable {w : Nat} {a b x y : BitVec w} {P₁ P₂ : Prop}

@[ascend_pure] theorem abs_add (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_sub (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a - b) (x - y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_beq (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a == b) (x == y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_mul (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a * b) (x * y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_and (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a &&& b) (x &&& y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_cmp {cc : CondCode} {a b x y : BitVec 64}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (cc.cmp a b) (cc.cmp x y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_sib {t : MachineData} {k : Nat} {b i : Reg64} {d : Int64} {x y : BitVec 64}
    (hb : PureRefinement (t.regs.get64 b) x P₁ Eq) (hi : PureRefinement (t.regs.get64 i) y P₂ Eq) :
    PureRefinement (sib k b i d t) (x + y * BitVec.ofNat 64 k + BitVec.ofInt 64 d.toInt) (P₁ ∧ P₂) Eq :=
  fun ⟨hp₁, hp₂⟩ => by rw [sib, hb hp₁, hi hp₂]

@[ascend_pure] theorem abs_not {c d : Bool} (h : PureRefinement c d P₁ Eq) :
    PureRefinement (!c) (!d) P₁ Eq := fun hp => by
  rw [h hp]

@[ascend_pure low] theorem abs_refl {α : Type} {c : α} : PureRefinement c c True Eq :=
  PureRefinement.of_rel rfl

end

/-! ## Words as numbers

`WordNat x n` states that the word `x` holds the number `n`. Under `x ≐ₙ n`, an addition of words
abstracts to the addition of the numbers, and a comparison of words abstracts to the comparison of
the numbers with the range of the numbers as its precondition. -/

def WordNat {w : Nat} (x : BitVec w) (n : Nat) : Prop := x = BitVec.ofNat w n

scoped notation:50 c:51 " ≐ₙ " x:51 => PureRefinement c x True WordNat

theorem beq_eq_true_eq {α : Type} [BEq α] [LawfulBEq α] (a b : α) : ((a == b) = true) = (a = b) :=
  propext beq_iff_eq

theorem bne_eq_true_eq {α : Type} [BEq α] [LawfulBEq α] (a b : α) : ((a != b) = true) = ¬a = b :=
  propext bne_iff_ne

section
variable {w : Nat} {x y : BitVec w} {i j : Nat} {P₁ P₂ : Prop}

@[ascend_pure] theorem absN_ofNat {n : Nat} : PureRefinement (BitVec.ofNat w n) n True WordNat :=
  PureRefinement.of_rel rfl

@[ascend_pure] theorem absN_add (h₁ : PureRefinement x i P₁ WordNat) (h₂ : PureRefinement y j P₂ WordNat) :
    PureRefinement (x + y) (i + j) (P₁ ∧ P₂) WordNat := fun ⟨hp₁, hp₂⟩ => by
  rw [WordNat, h₁ hp₁, h₂ hp₂, BitVec.ofNat_add]

theorem ofNat_eq_ofNat_iff {n m : Nat} (hn : n < 2 ^ w) (hm : m < 2 ^ w) :
    BitVec.ofNat w n = BitVec.ofNat w m ↔ n = m := by
  rw [BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hm]

@[ascend_pure] theorem absN_sub (h₁ : PureRefinement x i P₁ WordNat) (h₂ : PureRefinement y j P₂ WordNat) :
    PureRefinement (x - y) (i - j) (P₁ ∧ P₂ ∧ j ≤ i ∧ i < 2 ^ w) WordNat :=
  fun ⟨hp₁, hp₂, hji, hi⟩ => by
    rw [WordNat, h₁ hp₁, h₂ hp₂]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega : j < 2 ^ w), Nat.mod_eq_of_lt (by omega : i - j < 2 ^ w),
      show 2 ^ w - j + i = (i - j) + 2 ^ w by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

@[ascend_pure high] theorem absN_beq (h₁ : PureRefinement x i P₁ WordNat)
    (h₂ : PureRefinement y j P₂ WordNat) :
    PureRefinement (x == y) (i == j) (P₁ ∧ P₂ ∧ i < 2 ^ w ∧ j < 2 ^ w) Eq :=
  fun ⟨hp₁, hp₂, hi, hj⟩ => by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁ hp₁, h₂ hp₂, ofNat_eq_ofNat_iff hi hj]

end

section
variable {a b : BitVec 64} {n m : Nat} {P₁ P₂ : Prop}

@[ascend_pure high] theorem absN_cmp_nz (h₁ : PureRefinement a n P₁ WordNat)
    (h₂ : PureRefinement b m P₂ WordNat) :
    PureRefinement (CondCode.nz.cmp a b) (n != m) (P₁ ∧ P₂ ∧ n < 2 ^ 64 ∧ m < 2 ^ 64) Eq :=
  fun ⟨hp₁, hp₂, hn, hm⟩ => by
    rw [Bool.eq_iff_iff, CondCode.cmp_nz_eq_true, h₁ hp₁, h₂ hp₂, bne_iff_ne, ne_eq, ne_eq,
      ofNat_eq_ofNat_iff hn hm]

@[ascend_pure high] theorem absN_cmp_z_self_zero (h : PureRefinement a n P₁ WordNat) :
    PureRefinement (CondCode.z.cmp (a &&& a) 0#64) (n == 0) (P₁ ∧ n < 2 ^ 64) Eq :=
  fun ⟨hp, hn⟩ => by
    rw [Bool.eq_iff_iff, CondCode.cmp_z_eq_true, BitVec.and_self, h hp, beq_iff_eq]
    exact ofNat_eq_ofNat_iff hn (by omega)

@[ascend_pure high] theorem absN_cmp_le_self_zero (h : PureRefinement a n P₁ WordNat) :
    PureRefinement (CondCode.le.cmp (a &&& a) 0#64) (n == 0) (P₁ ∧ n < 2 ^ 63) Eq :=
  fun ⟨hp, hn⟩ => by
    rw [Bool.eq_iff_iff, CondCode.cmp_le_eq_true, BitVec.and_self, h hp, beq_iff_eq,
      BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, BitVec.toInt_zero]
    split <;> omega

end

/-! ## Steps -/

attribute [ascend] wrp_bind

section
variable {Q : Unit → BitVec 64 → MachineData → Prop} {Qu : Unit → Unit → MachineData → Prop}
  {E : (CfgLabel → CfgLabel → MachineData → Prop) × EStack⟨⟩}

@[ascend] theorem wrp_pure_unit :
    Qu () () ⊑ wrp (ofStateRepr MachineData.dmem) (pure () : BlockM MachineData Unit)
      (pure () : BlockM DataMem Unit) Qu E :=
  wrp_pure () ()

@[ascend] theorem wrp_loadReg_load (n : Nat) (r : Reg64) (a : MachineData → BitVec 64)
    (e : BitVec 64 → MachineData → BitVec 64) (pa : BitVec 64) :
    (fun t => a t ≐ pa ∧
      (loadOk n a t → ∀ w, word n (a t) t ≐ w → Q () w (loadReg n r a e t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (loadOk n a) (loadReg n r a e))
          (load n pa) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_load] at ht
  obtain ⟨⟨ha, hk⟩, hl, hq⟩ := ht
  have ha : a t = pa := ha trivial
  have hg : loadOk n a t := by rw [loadOk, ha]; exact hl
  rw [wp_modifyIf, Concretization.post_pi]
  refine ⟨hg, _, hk hg _ (PureRefinement.of_rel ?_), hq⟩
  rw [word, ha]

@[ascend] theorem wrp_storeWord_store (n : Nat) (a v : MachineData → BitVec 64) (sp pa pv : BitVec 64) :
    (fun t => t.regs.get64 .rsp ≐ sp ∧ a t ≐ pa ∧ v t ≐ pv ∧
      (storeOk n a t → Qu () () (storeWord n a v t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (storeOk n a) (storeWord n a v))
          (store n sp pa pv) Qu E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_store] at ht
  obtain ⟨⟨hsp, ha, hv, hk⟩, ⟨hl, hd⟩, hq⟩ := ht
  have hsp : t.regs.get64 .rsp = sp := hsp trivial
  have ha : a t = pa := ha trivial
  have hv : v t = pv := hv trivial
  have hg : storeOk n a t := by rw [storeOk, loadOk, ha, hsp]; exact ⟨hl, hd⟩
  rw [wp_modifyIf, Concretization.post_pi]
  refine ⟨hg, (), hk hg, ?_⟩
  simp only [ofStateRepr_pred, storeWord, ha, hv]
  exact hq

@[ascend] theorem wrp_peek_pure {γ : Type} {Qγ : γ → γ → MachineData → Prop} (c : MachineData → γ) (b : γ) :
    (fun t => c t ≐ b ∧ ∀ z, c t ≐ z → Qγ (c t) z t)
      ⊑ wrp (ofStateRepr MachineData.dmem) (peek c) (pure b : BlockM DataMem γ) Qγ E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at ht
  obtain ⟨⟨hb, hq⟩, hqa⟩ := ht
  rw [wp_peek, Concretization.post_pi]
  exact ⟨b, hq b hb, hqa⟩

end

/-! ## Control -/

section
variable {σc σa : Type} {view : σc → σa} {E : (CfgLabel → CfgLabel → σc → Prop) × EStack⟨⟩}

theorem wrp_forIn_lockstep_bind_unit {βc βa : Type} (R : βc → σc → βa → Prop) (cinit : βc)
    (ainit : βa) {fc : Unit → βc → BlockM σc (ForInStep βc)}
    {fa : βa → BlockM σa (ForInStep βa)} {Q : Unit → Unit → σc → Prop}
    (hbody : ∀ c i, (fun t => R c t i) ⊑ wrp (ofStateRepr view) (fc () c) (fa i)
      (fun rc ra t => match rc with
        | .yield c' => ∃ a', R c' t a' ∧ ra = .yield a'
        | .done _ => ∃ a', Q () () t ∧ ra = .done a') E) :
    (fun t => R cinit t ainit) ⊑ wrp (ofStateRepr view)
      (FixLoop.mk.forIn cinit fc >>= fun _ => pure ())
      (FixLoop.mk.forIn ainit (fun _ v => fa v) >>= fun _ => pure ()) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq,
    WPMonadExact.wp_pure_eq] at ht
  have h := wrp_transport (wrp_forIn_lockstep R cinit ainit (fa := fa)
    (Q := fun _ _ t => Q () () t) fun c i => PartialOrder.rel_trans (hbody c i)
      (wrp_mono_post fun rc ra t h => by cases rc <;> exact h))
    (fun _ => Qa ()) Ea t
    (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ht)
  rw [WPMonadExact.wp_bind_eq]
  refine WP.wp_monotone_post (x := FixLoop.mk.forIn cinit fc) ?_ t h
  intro u t' h'
  rw [Concretization.post_pi] at h'
  obtain ⟨_, hq, hqa⟩ := h'
  simp only [WPMonadExact.wp_pure_eq]
  rw [Concretization.post_pi]
  exact ⟨(), hq, hqa⟩

@[ascend low] theorem wrp_pure_val {γ : Type} {Q : γ → γ → σc → Prop} (c b : γ) (P : Prop) :
    (fun t => PureRefinement c b P Eq ∧ P ∧ ∀ z, c ≐ z → Q c z t)
      ⊑ wrp (ofStateRepr view) (pure c : BlockM σc γ) (pure b : BlockM σa γ) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at ht ⊢
  obtain ⟨⟨hb, hP, hq⟩, hqa⟩ := ht
  rw [Concretization.post_pi]
  exact ⟨b, hq b (PureRefinement.of_rel (hb hP)), hqa⟩

end

section
variable {AV : Type} {Qu : Unit → AV → MachineData → Prop}
  {E : (CfgLabel → CfgLabel → MachineData → Prop) × EStack⟨⟩}

theorem wrp_forIn_lockstep_unit {βa : Type} (R : MachineData → βa → Prop) (ab : βa)
    {fc : Unit → PUnit → BlockM MachineData (ForInStep PUnit)}
    {fa : βa → BlockM DataMem (ForInStep βa)}
    {Q : PUnit → Unit → MachineData → Prop}
    (hbody : ∀ v, (fun t => R t v) ⊑ wrp (ofStateRepr MachineData.dmem) (fc () PUnit.unit) (fa v)
      (fun rc ra t => match rc with
        | .yield _ => ∃ a', R t a' ∧ ra = .yield a'
        | .done u => ∃ a', Q u () t ∧ ra = .done a') E) :
    (fun t => R t ab) ⊑ wrp (ofStateRepr MachineData.dmem) (FixLoop.mk.forIn PUnit.unit fc)
      (FixLoop.mk.forIn ab (fun _ v => fa v) >>= fun _ => pure ()) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq,
    WPMonadExact.wp_pure_eq] at ht
  have h := wrp_transport
    (wrp_forIn_lockstep (fun _ t a => R t a) PUnit.unit ab (fa := fa)
      (Q := fun u _ t => Q u () t) fun _ v => PartialOrder.rel_trans (hbody v)
        (wrp_mono_post fun rc ra t h => by cases rc <;> exact h))
      (fun _ => Qa ()) Ea t
    (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ht)
  refine WP.wp_monotone_post (x := FixLoop.mk.forIn PUnit.unit fc) ?_ t h
  intro u t' h'
  rw [Concretization.post_pi] at h' ⊢
  obtain ⟨_, hq, hqa⟩ := h'
  exact ⟨(), hq, hqa⟩

@[ascend] theorem wrp_condState {σc σa CV AV : Type} {view : σc → σa}
    {E : (CfgLabel → CfgLabel → σc → Prop) × EStack⟨⟩} {Q : CV → AV → σc → Prop} {c : σc → Bool}
    {x y : BlockM σc CV} {ax ay : BlockM σa AV} (b : Bool) (P : Prop) :
    (fun t => PureRefinement (c t) b P Eq ∧ P ∧
      (b = true → wrp (ofStateRepr view) x ax Q E t) ∧
      (b = false → wrp (ofStateRepr view) y ay Q E t))
      ⊑ wrp (ofStateRepr view) (condState c x y) (condState (fun _ => b) ax ay) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_condState] at ht
  obtain ⟨⟨hb, hP, hx, hy⟩, hw⟩ := ht
  have hb : c t = b := hb hP
  rw [wp_condState]
  cases b with
  | true =>
    simp only [hb, ↓reduceIte] at hw ⊢
    exact wrp_transport (P := wrp (ofStateRepr view) x ax Q E) PartialOrder.rel_refl Qa Ea t
      (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ⟨hx rfl, hw⟩)
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    exact wrp_transport (P := wrp (ofStateRepr view) y ay Q E) PartialOrder.rel_refl Qa Ea t
      (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ⟨hy rfl, hw⟩)

@[ascend high] theorem wrp_stutter_bind {CV : Type} {Q : CV → AV → MachineData → Prop}
    (f : MachineData → MachineData)
    {k : Unit → BlockM MachineData CV} {a : BlockM DataMem AV} (hf : ∀ t, (f t).dmem = t.dmem) :
    (fun t => wrp (ofStateRepr MachineData.dmem) (k ()) a Q E (f t))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (fun _ => True) f >>= k) a Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at ht
  obtain ⟨hk, hw⟩ := ht
  rw [WPMonadExact.wp_bind_eq, wp_modifyIf]
  refine ⟨trivial, wrp_transport (P := wrp (ofStateRepr MachineData.dmem) (k ()) a Q E)
    PartialOrder.rel_refl Qa Ea (f t) ?_⟩
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, hf]
  exact ⟨hk, hw⟩

@[ascend] theorem wrp_exitIf_assume {CV AV : Type} {Q : CV → AV → MachineData → Prop}
    (a : MachineData → BitVec 64) (f : MachineData → MachineData) (l : CfgLabel) (pa : BitVec 64)
    (hf : ∀ t, (f t).dmem = t.dmem) :
    (fun t => a t ≐ pa ∧ (loadOk 8 a t → E.1 l l (f t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (exitIf (loadOk 8 a) f l : BlockM MachineData CV)
          (do StateT.assume (fun m => (Mem.loadInt m pa 8).isSome = true); throw l : BlockM DataMem AV)
          Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_assume_throw] at ht
  obtain ⟨⟨ha, hk⟩, hl, he⟩ := ht
  have ha : a t = pa := ha trivial
  have hg : loadOk 8 a t := by rw [loadOk, ha]; exact hl
  rw [wp_exitIf]
  refine ⟨hg, ?_⟩
  simp only [EPostsConcretization.ePosts_cons]
  rw [Concretization.post_pi]
  refine ⟨l, hk hg, ?_⟩
  simp only [ofStateRepr_pred, hf]
  exact he

end


end Ascent.Kraken
