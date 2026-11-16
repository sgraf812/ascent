import Demo.RegsCall
import Demo.Frame

/-!
# Calls with the frame split off

`callFrame bs p k` is the call over the split state, for the return slot `p`, a region and an
address. It pushes an unknown word `v` into the slot (`pushUnknownFrame`), runs the abstract callee
`k v` with `v` as its return address, and continues when `k` throws `v`. The call rule refines
`callRegs r kL` to `callFrame bs p kF` from the refinement of `kL v` to `kF v` for every `v`, a
premise that a `Refinement` spec of the callee closes, and from `KeepsFrame (kF v)`: the callee
leaves the frame of the caller unchanged. The caller continues with the exit relation of the
callee and with the frame it had after the push.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Kraken

/-- `x` leaves the frame of the state unchanged. -/
def KeepsFrame {α : Type} (x : BlockM FState α) : Prop :=
  ∀ (Q : α → FState → Prop) (E : (Int64 → FState → Prop) × EStack⟨⟩) s, wp x Q E s →
    wp x (fun a s' => Q a s' ∧ s'.frame = s.frame)
      (fun l s' => E.1 l s' ∧ s'.frame = s.frame, E.2) s

section
variable {α β : Type}

theorem KeepsFrame.pure (a : α) : KeepsFrame (pure a : BlockM FState α) = True :=
    eq_true fun Q E s hw => by
  rw [WPMonadExact.wp_pure_eq] at hw ⊢
  exact ⟨hw, rfl⟩

theorem KeepsFrame.throw (l : Int64) : KeepsFrame (throw l : BlockM FState α) = True :=
    eq_true fun Q E s hw => by
  rw [wp_throw_block] at hw ⊢
  exact ⟨hw, rfl⟩

theorem KeepsFrame.bind {x : BlockM FState α} {k : α → BlockM FState β} (hx : KeepsFrame x)
    (hk : ∀ a, KeepsFrame (k a)) : KeepsFrame (x >>= k) = True := eq_true fun Q E s hw => by
  rw [WPMonadExact.wp_bind_eq] at hw ⊢
  refine WP.wp_monotone (x := x) (fun a t ⟨ht, hf⟩ => ?_)
    (Prod.mk_le _ _ _ (fun _ _ h => h) PartialOrder.rel_refl) s (hx _ _ s hw)
  refine WP.wp_monotone (x := k a) (fun b u ⟨hu, hf'⟩ => ⟨hu, hf'.trans hf⟩) ?_ t (hk a _ _ t ht)
  exact Prod.mk_le _ _ _ (fun l u ⟨hu, hf'⟩ => ⟨hu, hf'.trans hf⟩) PartialOrder.rel_refl

theorem KeepsFrame.zoom_dmem (x : BlockM DataMem α) : KeepsFrame (zoom .dmem x) = True :=
    eq_true fun Q E s hw => by
  rw [wp_zoom] at hw ⊢
  refine WP.wp_monotone (x := x) (fun a m h => ⟨h, rfl⟩) ?_ _ hw
  refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
  intro l m h
  exact ⟨h, rfl⟩

theorem KeepsFrame.assert_bind (g : FState → Prop) {x : BlockM FState α} (hx : KeepsFrame x) :
    KeepsFrame (do StateT.assert g; x) = True := eq_true fun Q E s hw => by
  rw [wp_assert_bind] at hw ⊢
  exact ⟨hw.1, hx _ _ s hw.2⟩

theorem KeepsFrame.loadIn_dmem (bs : List (BitVec 64 × Nat)) (n : Nat) (a : BitVec 64) :
    KeepsFrame (loadIn bs .dmem n a) = True := by
  unfold loadIn
  exact KeepsFrame.assert_bind _ (of_eq_true (KeepsFrame.zoom_dmem _))

theorem KeepsFrame.storeIn_dmem (bs : List (BitVec 64 × Nat)) (n : Nat) (a v : BitVec 64) :
    KeepsFrame (storeIn bs .dmem n a v) = True := by
  unfold storeIn
  exact KeepsFrame.assert_bind _ (of_eq_true (KeepsFrame.zoom_dmem _))

theorem KeepsFrame.condState (c : FState → Bool) {x y : BlockM FState α} (hx : KeepsFrame x)
    (hy : KeepsFrame y) : KeepsFrame (condState c x y) = True := eq_true fun Q E s hw => by
  by_cases h : c s = true
  · simp only [wp_condState, h, ↓reduceIte] at hw ⊢
    exact hx _ _ s hw
  · simp only [wp_condState, h, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    exact hy _ _ s hw

end

/-- Push an unknown 8-byte word into the slot `p` and return it. -/
def pushUnknownFrame (bs : List (BitVec 64 × Nat)) (p : Region × BitVec 64) : BlockM FState Int64 :=
  ExceptT.mk fun s => do
    Demonic.assert (DmemOk bs p.2 8 p.1 ∧ (Mem.loadInt (s.get p.1) p.2 8).isSome = true)
    let v : Int64 ← Demonic.unknown
    pure (.ok v, s.set p.1 ((s.get p.1).storeInt p.2 8 (Int64.toBitVec v).toInt))

theorem wp_pushUnknownFrame_fun (bs : List (BitVec 64 × Nat)) (p : Region × BitVec 64)
    (Q : Int64 → FState → Prop) (E : (Int64 → FState → Prop) × EStack⟨⟩) :
    wp (pushUnknownFrame bs p) Q E = fun s =>
      (DmemOk bs p.2 8 p.1 ∧ (Mem.loadInt (s.get p.1) p.2 8).isSome = true) ∧
      ∀ v, Q v (s.set p.1 ((s.get p.1).storeInt p.2 8 (Int64.toBitVec v).toInt)) :=
  funext fun _ => propext
    ⟨fun ⟨hm, h⟩ => ⟨hm, fun v => h v trivial⟩, fun ⟨hm, h⟩ => ⟨hm, fun v _ => h v⟩⟩

noncomputable def callFrame (bs : List (BitVec 64 × Nat)) (p : Region × BitVec 64)
    (k : Int64 → BlockM FState Unit) : BlockM FState Unit := do
  let v ← pushUnknownFrame bs p
  tryCatch (do k v; modifyIf (fun _ => False) id) fun l => modifyIf (fun _ => l = v) id

section
variable {Q : Unit → Unit → DataMem → Prop} {E : (Int64 → Int64 → DataMem → Prop) × EStack⟨⟩}

theorem wrp_callRegs_callFrame {bs : List (BitVec 64 × Nat)} {kL : Int64 → BlockM DataMem Unit}
    {kF : Int64 → BlockM FState Unit} {Pre : Int64 → DataMem → Prop}
    {Qc : Unit → Unit → DataMem → Prop} {Ec : Int64 → Int64 → DataMem → Prop}
    (r : BitVec 64) (reg : Region) (x : BitVec 64) (P : Prop)
    (hk : ∀ v : Int64, ⦃Pre v⦄ (kL v) ⪯[ofStateRepr (FState.split bs)] (kF v) ⦃Qc; (Ec, estack⟨⟩)⦄)
    (hkeep : ∀ v, KeepsFrame (kF v))
    (hex : ∀ c l m, Ec c l m → c = l) :
    (fun m => PureRefinement (r - 8#64) (reg, x) P (Located bs 8) ∧ P ∧
      (DmemOk bs (r - 8#64) 8 reg →
        (∀ v, Pre v (m.storeInt (r - 8#64) 8 v.toBitVec.toInt)) ∧
        ∀ (v : Int64) m' c l, Ec c l m' →
          m'.restrict bs = (m.storeInt (r - 8#64) 8 v.toBitVec.toInt).restrict bs → Q () () m'))
      ⊑ wrp (ofStateRepr (FState.split bs)) (callRegs r kL) (callFrame bs (reg, x) kF) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro m hm
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at hm
  obtain ⟨⟨hl, hP, hq⟩, hw⟩ := hm
  obtain ⟨hrx, hf⟩ := hl hP
  subst hrx
  simp only [callFrame, WPMonadExact.wp_bind_eq, wp_pushUnknownFrame_fun, BlockLoop.wp_tryCatch,
    wp_modifyIf_fun] at hw
  obtain ⟨⟨hd, hm⟩, hw⟩ := hw
  have hr := InRegion.of_ok hf hd
  obtain ⟨hpre, hQ⟩ := hq hd
  rw [hr.loadInt] at hm
  simp only [callRegs, WPMonadExact.wp_bind_eq, wp_pushUnknownRegs_fun, BlockLoop.wp_tryCatch,
    wp_modifyIf_fun]
  refine ⟨hm, fun v => ?_⟩
  have hsplit := hr.split_storeInt (m := m) v.toBitVec.toInt
  have hwS := hw v
  rw [← hsplit] at hwS
  dsimp only [id] at hwS
  have hkp := hkeep v _ _ _ hwS
  let Qa' : Unit → FState → Prop := fun _ s' => (False ∧ Qa () s') ∧
    s'.frame = (FState.split bs (m.storeInt (r - 8#64) 8 v.toBitVec.toInt)).frame
  let Ea' : (Int64 → FState → Prop) × EStack⟨⟩ :=
    (fun l s' => (l = v ∧ Qa () s') ∧
      s'.frame = (FState.split bs (m.storeInt (r - 8#64) 8 v.toBitVec.toInt)).frame, Ea.2)
  have hc := wrp_transport (hk v).le_wrp Qa' Ea' (m.storeInt (r - 8#64) 8 v.toBitVec.toInt)
    (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ⟨hpre v, hkp⟩)
  refine WP.wp_monotone (x := kL v) ?_ ?_ _ hc
  · intro u m' hu
    simp only [Concretization.post_pi, ofStateRepr_pred, Qa', false_and, and_false,
      exists_false] at hu
  · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro c m' hc'
    simp only [Concretization.post_pi, ofStateRepr_pred, Ea'] at hc'
    obtain ⟨l, hE, ⟨hlv, hqa⟩, hfr⟩ := hc'
    refine ⟨?_, ?_⟩
    · exact (hex _ _ _ hE).trans hlv
    rw [Concretization.post_pi]
    exact ⟨(), hQ v m' c l hE hfr, hqa⟩

end

theorem wrp_pushUnknownFrame_frame {σa : Type} {view : DataMem → σa} {Q : Int64 → Unit → FState → Prop}
    {E : (Int64 → Int64 → FState → Prop) × EStack⟨⟩} (bs : List (BitVec 64 × Nat)) (x : BitVec 64) :
    (fun s => (Mem.loadInt s.frame x 8).isSome = true ∧
      ∀ v : Int64, Q v () (s.set .frame (Mem.storeInt s.frame x 8 (Int64.toBitVec v).toInt)))
      ⊑ wrp (ofStateRepr fun s : FState => view s.dmem) (pushUnknownFrame bs (.frame, x))
          (pure () : BlockM σa Unit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_pure_eq] at hs
  obtain ⟨⟨hm, hq⟩, hqa⟩ := hs
  rw [wp_pushUnknownFrame_fun]
  refine ⟨⟨trivial, hm⟩, fun v => ?_⟩
  rw [Concretization.post_pi]
  exact ⟨(), hq v, hqa⟩

attribute [ascend] wrp_pushUnknownFrame_frame

/-! ## Inlining a callee

A call of a callee that throws only at its return is the callee's body: the handler of the call
catches the return and checks the return address, which the body threw. -/

theorem tryCatch_bind_of_throwsOnly {σ α β : Type} {x : BlockM σ α}
    (hx : ThrowsOnly (fun _ _ => False) x) (k : α → BlockM σ β) (h : Int64 → BlockM σ β) :
    tryCatch (x >>= k) h = x >>= fun a => tryCatch (k a) h := by
  apply BlockLoop.ext_wp <;> intro Q E s hw <;>
    simp only [wp_tryCatch_fun, WPMonadExact.wp_bind_eq] at hw ⊢ <;>
    (have h1 := hx _ _ s hw
     exact WP.wp_monotone (x := x) (fun _ _ h => h)
       (Prod.mk_le _ _ _ (fun _ _ h => h.1.elim) PartialOrder.rel_refl) s h1)

theorem modifyIf_true_id {σ : Type} :
    modifyIf (fun _ : σ => True) id = (pure () : BlockM σ Unit) := by
  apply BlockLoop.ext_wp <;> intro Q E s hw <;>
    simp only [wp_modifyIf, WPMonadExact.wp_pure_eq, true_and, id] at hw ⊢ <;> exact hw

theorem ThrowsOnly.loadIn {P : Int64 → FState → Prop} (bs : List (BitVec 64 × Nat)) (r : Region)
    (n : Nat) (a : BitVec 64) : ThrowsOnly P (loadIn bs r n a) = True := eq_true fun Q E s hw => by
  unfold Kraken.loadIn at hw ⊢
  rw [wp_assert_bind, wp_zoom, wp_load] at hw ⊢
  exact hw

theorem ThrowsOnly.storeIn {P : Int64 → FState → Prop} (bs : List (BitVec 64 × Nat)) (r : Region)
    (n : Nat) (a v : BitVec 64) : ThrowsOnly P (storeIn bs r n a v) = True :=
    eq_true fun Q E s hw => by
  unfold Kraken.storeIn at hw ⊢
  rw [wp_assert_bind, wp_zoom, wp_store] at hw ⊢
  exact hw

theorem retAddrAt_eq_of_restrict_eq {bs : List (BitVec 64 × Nat)} {m m' : DataMem} {p : BitVec 64}
    (h : m'.restrict bs = m.restrict bs) (hi : Mem.Blocks.Inside p 8 bs) :
    retAddrAt m' p = retAddrAt m p := by
  rw [retAddrAt_eq, retAddrAt_eq, ← Mem.loadInt_restrict_of_inside hi, h,
    Mem.loadInt_restrict_of_inside hi]

grind_pattern retAddrAt_eq_of_restrict_eq => retAddrAt m' p, Mem.restrict m' bs, Mem.restrict m bs

end Ascent.Kraken
