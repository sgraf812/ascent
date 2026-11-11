import Demo.L1
import Ascent.FixLoop
import Ascent.FixLoop.Delab

/-!
# Structuring a block loop by rewriting

The block loop of a text is structured by `cfgLoop_header` of `Ascent.BlockLoop`, applied at every
label: each label becomes the header of a `repeat'` loop over the other blocks that continues on a
return to the label in a state with the stack test. The equations of this file push the loop's
`try` into the blocks, through a mapped computation as well, until it meets the throws.

A jump to a label assumes the stack test, and a handler or a loop that it meets tests it again;
`modifyIf_stay_bind_condState` drops the second test. A return throws the return address `a` after
it sets the stack pointer above the frame, so a header handler and a block loop both throw `a` on
(`tryCatch_exitIf_handler`, `tryCatch_exitIf_cfgLoop`). Two labels of a separated text have distinct
addresses (`Program.label_eq_false`).

A handler crosses an inner loop that never throws its label (`tryCatch_forIn_bind`, with the
exception effect `ThrowsOnly` as premise). The marks `done <$>` then collect at the root of a body
(`pure_done_eq`, `bind_map`, `condState_map`, `throw_label_step`), an exit absorbs a mark
(`map_exitIf`, `map_bind_exitIf`), and a loop whose body never continues collapses to its body
(`forIn_map_done`, `forIn_bind_exitIf`, `forIn_exitIf`).
-/

open Std.WP Lean.Order Ascent

namespace Ascent.Kraken

theorem BlockM.ext_wp {σ α : Type} {x y : BlockM σ α}
    (h : ∀ (Q : α → σ → Prop) (E : (Int64 → σ → Prop) × EStack⟨⟩) s, wp x Q E s → wp y Q E s)
    (h' : ∀ (Q : α → σ → Prop) (E : (Int64 → σ → Prop) × EStack⟨⟩) s, wp y Q E s → wp x Q E s) :
    x = y :=
  BlockLoop.ext_wp h h'

/-! ## Pushing `try` into a block -/

section
variable {σ β : Type}

theorem tryCatch_bind_assoc {α γ : Type} (x : BlockM σ α) (f : α → BlockM σ γ) (k : γ → BlockM σ β)
    (h : Int64 → BlockM σ β) :
    tryCatch ((x >>= f) >>= k) h = tryCatch (x >>= fun a => f a >>= k) h := by
  rw [bind_assoc]

theorem tryCatch_modifyIf_bind (g : σ → Prop) (f : σ → σ) (k : Unit → BlockM σ β)
    (h : Int64 → BlockM σ β) :
    tryCatch (AInstr.modifyIf g f >>= k) h = AInstr.modifyIf g f >>= fun a => tryCatch (k a) h := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [BlockLoop.wp_tryCatch, WPMonadExact.wp_bind_eq, AInstr.wp_modifyIf] <;> exact id

theorem tryCatch_peek_bind {γ : Type} (c : σ → γ) (k : γ → BlockM σ β) (h : Int64 → BlockM σ β) :
    tryCatch (AInstr.peek c >>= k) h = AInstr.peek c >>= fun z => tryCatch (k z) h := rfl

theorem tryCatch_exitIf_handle {α : Type} (g : σ → Prop) (f : σ → σ) (l : Int64)
    (h : Int64 → BlockM σ α) :
    tryCatch (AInstr.exitIf g f l : BlockM σ α) h = AInstr.modifyIf g f >>= fun _ => h l := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [BlockLoop.wp_tryCatch, AInstr.wp_exitIf, WPMonadExact.wp_bind_eq, AInstr.wp_modifyIf] <;>
    exact id

theorem tryCatch_branch_bind (st c : σ → Bool) (l : Int64) (k : Unit → BlockM σ β)
    (h : Int64 → BlockM σ β) :
    tryCatch (AInstr.branch st c l >>= k) h
      = condState c (AInstr.modifyIf (fun s => st s = true) id >>= fun _ => h l) (tryCatch (k ()) h) := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [BlockLoop.wp_tryCatch, WPMonadExact.wp_bind_eq, AInstr.wp_branch, wp_condState,
      AInstr.wp_modifyIf, id] <;> split <;> exact id

theorem tryCatch_branch (st c : σ → Bool) (l : Int64) (h : Int64 → BlockM σ Unit) :
    tryCatch (AInstr.branch st c l) h
      = condState c (AInstr.modifyIf (fun s => st s = true) id >>= fun _ => h l) (pure ()) := by
  rw [← bind_pure_unit (x := AInstr.branch st c l), tryCatch_branch_bind, BlockLoop.tryCatch_pure]

theorem tryCatch_ite (p : Prop) [Decidable p] (x y : BlockM σ β) (h : Int64 → BlockM σ β) :
    tryCatch (if p then x else y) h = if p then tryCatch x h else tryCatch y h := by
  split <;> rfl

theorem tryCatch_condState_bind {γ : Type} (c : σ → Bool) (x y : BlockM σ γ) (k : γ → BlockM σ β)
    (h : Int64 → BlockM σ β) :
    tryCatch (condState c x y >>= k) h = condState c (tryCatch (x >>= k) h) (tryCatch (y >>= k) h) := by
  rw [condState_bind, tryCatch_condState]

theorem modifyIf_true_bind_condState (f : σ → σ) (c : σ → Bool) (x y : BlockM σ β) :
    (AInstr.modifyIf (fun _ => True) f >>= fun _ => condState c x y)
      = condState (fun st => c (f st)) (AInstr.modifyIf (fun _ => True) f >>= fun _ => x)
          (AInstr.modifyIf (fun _ => True) f >>= fun _ => y) := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [WPMonadExact.wp_bind_eq, AInstr.wp_modifyIf, wp_condState] <;> split <;> simp_all

theorem modifyIf_id_bind_condState (g : σ → Prop) (c : σ → Bool) (x y : BlockM σ β) :
    (AInstr.modifyIf g id >>= fun _ => condState c x y)
      = condState c (AInstr.modifyIf g id >>= fun _ => x) (AInstr.modifyIf g id >>= fun _ => y) := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [WPMonadExact.wp_bind_eq, AInstr.wp_modifyIf, wp_condState, id] <;> split <;> simp_all

theorem modifyIf_stay_bind_condState (c : σ → Bool) (x y : BlockM σ β) :
    (AInstr.modifyIf (fun s => c s = true) id >>= fun _ => condState c x y)
      = AInstr.modifyIf (fun s => c s = true) id >>= fun _ => x := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [WPMonadExact.wp_bind_eq, AInstr.wp_modifyIf, wp_condState, id] <;>
    rintro ⟨h, hw⟩ <;> simp_all

theorem tryCatch_exitIf_handler {α : Type} (g : σ → Prop) (f : σ → σ) (a h : Int64) (c : σ → Bool)
    (x : BlockM σ α) (hc : ∀ s, c (f s) = false) :
    tryCatch (AInstr.exitIf g f a : BlockM σ α)
        (fun l' => if l' = h then condState c x (throw l') else throw l')
      = AInstr.exitIf g f a := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [BlockLoop.wp_tryCatch, AInstr.wp_exitIf] <;> rintro ⟨hg, hw⟩ <;> refine ⟨hg, ?_⟩ <;>
    split at * <;> simp_all [wp_condState, BlockLoop.wp_throw]

theorem tryCatch_exitIf_cfgLoop (g : σ → Prop) (f : σ → σ) (a : Int64) (c : σ → Bool)
    (T : Table Int64 (BlockM σ Unit)) (hc : ∀ s, c (f s) = false) :
    tryCatch (AInstr.exitIf g f a : BlockM σ Unit) (cfgLoop c T) = AInstr.exitIf g f a := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [BlockLoop.wp_tryCatch, AInstr.wp_exitIf, wp_cfgLoop_leave c T Q E (hc s)] <;> exact id

theorem pure_done_eq (u : PUnit) :
    (pure (ForInStep.done u) : BlockM σ (ForInStep PUnit)) = ForInStep.done <$> (pure u : BlockM σ PUnit) :=
  (map_pure _ _).symm

theorem map_exitIf {γ δ : Type} (f : γ → δ) (g : σ → Prop) (h : σ → σ) (l : Int64) :
    f <$> (AInstr.exitIf g h l : BlockM σ γ) = AInstr.exitIf g h l := by
  rw [map_eq_pure_bind, AInstr.exitIf_bind]

theorem tryCatch_map_bind {α γ δ : Type} (f : γ → δ) (x : BlockM σ α) (k : α → BlockM σ γ)
    (h : Int64 → BlockM σ δ) :
    tryCatch (f <$> (x >>= k)) h = tryCatch (x >>= fun a => f <$> k a) h := by
  rw [map_bind]

theorem tryCatch_map_condState {γ δ : Type} (f : γ → δ) (c : σ → Bool) (x y : BlockM σ γ)
    (h : Int64 → BlockM σ δ) :
    tryCatch (f <$> condState c x y) h = condState c (tryCatch (f <$> x) h) (tryCatch (f <$> y) h) := by
  rw [← condState_map, tryCatch_condState]

theorem tryCatch_map_throw {γ δ : Type} (f : γ → δ) (l : Int64) (h : Int64 → BlockM σ δ) :
    tryCatch (f <$> (throw l : BlockM σ γ)) h = h l := by
  rw [map_eq_pure_bind, BlockLoop.throw_bind, BlockLoop.tryCatch_throw]

theorem tryCatch_map_pure {γ δ : Type} (f : γ → δ) (a : γ) (h : Int64 → BlockM σ δ) :
    tryCatch (f <$> (pure a : BlockM σ γ)) h = f <$> (pure a : BlockM σ γ) := by
  rw [map_pure, BlockLoop.tryCatch_pure]

theorem tryCatch_map_modifyIf {δ : Type} (f : Unit → δ) (g : σ → Prop) (u : σ → σ)
    (h : Int64 → BlockM σ δ) :
    tryCatch (f <$> AInstr.modifyIf g u) h = f <$> AInstr.modifyIf g u := by
  rw [map_eq_pure_bind, ← bind_pure (AInstr.modifyIf g u >>= _), bind_assoc, tryCatch_modifyIf_bind]
  simp only [pure_bind, BlockLoop.tryCatch_pure, bind_pure_comp]

theorem throw_label_step [Host] (s : Label) :
    (throw (label s) : BlockM σ (ForInStep PUnit))
      = ForInStep.done <$> (throw (label s) : BlockM σ PUnit) := by
  rw [map_eq_pure_bind, BlockLoop.throw_bind]

theorem condState_exitIf_map {γ δ : Type} (c : σ → Bool) (g : σ → Prop) (h : σ → σ) (l : Int64)
    (f : γ → δ) (y : BlockM σ γ) :
    condState c (AInstr.exitIf g h l) (f <$> y) = f <$> condState c (AInstr.exitIf g h l) y := by
  rw [← condState_map, map_exitIf]

theorem condState_map_exitIf {γ δ : Type} (c : σ → Bool) (g : σ → Prop) (h : σ → σ) (l : Int64)
    (f : γ → δ) (x : BlockM σ γ) :
    condState c (f <$> x) (AInstr.exitIf g h l) = f <$> condState c x (AInstr.exitIf g h l) := by
  rw [← condState_map, map_exitIf]

theorem exitIf_step (g : σ → Prop) (h : σ → σ) (l : Int64) :
    (AInstr.exitIf g h l : BlockM σ (ForInStep PUnit))
      = ForInStep.done <$> (AInstr.exitIf g h l : BlockM σ PUnit) := by
  rw [map_exitIf]

theorem map_bind_exitIf {α γ δ : Type} (f : γ → δ) (x : BlockM σ α) (g : σ → Prop) (h : σ → σ)
    (l : α → Int64) :
    f <$> (x >>= fun a => (AInstr.exitIf g h (l a) : BlockM σ γ)) = x >>= fun a => AInstr.exitIf g h (l a) := by
  rw [map_bind]
  simp only [map_exitIf]

theorem condState_bind_exitIf_map {α γ δ : Type} (c : σ → Bool) (x : BlockM σ α) (g : σ → Prop)
    (h : σ → σ) (l : α → Int64) (f : γ → δ) (y : BlockM σ γ) :
    condState c (x >>= fun a => AInstr.exitIf g h (l a)) (f <$> y)
      = f <$> condState c (x >>= fun a => AInstr.exitIf g h (l a)) y := by
  rw [← condState_map, map_bind_exitIf]

theorem condState_map_bind_exitIf {α γ δ : Type} (c : σ → Bool) (x : BlockM σ α) (g : σ → Prop)
    (h : σ → σ) (l : α → Int64) (f : γ → δ) (y : BlockM σ γ) :
    condState c (f <$> y) (x >>= fun a => AInstr.exitIf g h (l a))
      = f <$> condState c y (x >>= fun a => AInstr.exitIf g h (l a)) := by
  rw [← condState_map, map_bind_exitIf]

theorem forIn_bind_exitIf {α β : Type} (b : β) (x : BlockM σ α) (g : σ → Prop) (h : σ → σ)
    (l : α → Int64) :
    FixLoop.mk.forIn b (fun _ _ => x >>= fun a => (AInstr.exitIf g h (l a) : BlockM σ (ForInStep β)))
      = x >>= fun a => AInstr.exitIf g h (l a) := by
  rw [FixLoop.forIn_eq, bind_assoc]
  simp only [AInstr.exitIf_bind]

theorem forIn_bind_exitIf_eta {β : Type} (b : β) (x : BlockM σ Int64) (g : σ → Prop) (h : σ → σ) :
    FixLoop.mk.forIn b (fun _ _ => x >>= (AInstr.exitIf g h : Int64 → BlockM σ (ForInStep β)))
      = x >>= AInstr.exitIf g h :=
  forIn_bind_exitIf b x g h id

theorem forIn_bind_bind_exitIf {α γ β : Type} (b : β) (x : BlockM σ α) (y : α → BlockM σ γ)
    (g : σ → Prop) (h : σ → σ) (l : γ → Int64) :
    FixLoop.mk.forIn b (fun _ _ => x >>= fun a => y a >>= fun c =>
        (AInstr.exitIf g h (l c) : BlockM σ (ForInStep β)))
      = x >>= fun a => y a >>= fun c => AInstr.exitIf g h (l c) := by
  rw [FixLoop.forIn_eq, bind_assoc]
  simp only [bind_assoc, AInstr.exitIf_bind]

theorem forIn_bind3_exitIf {β : Type} {γ1 γ2 : Type} (x1 : BlockM σ γ1) (x2 : γ1 → BlockM σ γ2) (b : β) (g : σ → Prop) (h : σ → σ)
    (l : γ2 → Int64) :
    FixLoop.mk.forIn b (fun _ _ => x1 >>= fun a1 => x2 a1 >>= fun a2 =>
        (AInstr.exitIf g h (l a2) : BlockM σ (ForInStep β)))
      = x1 >>= fun a1 => x2 a1 >>= fun a2 => AInstr.exitIf g h (l a2) := by
  rw [FixLoop.forIn_eq]
  simp only [bind_assoc, AInstr.exitIf_bind]

theorem forIn_bind4_exitIf {β : Type} {γ1 γ2 γ3 : Type} (x1 : BlockM σ γ1) (x2 : γ1 → BlockM σ γ2) (x3 : γ2 → BlockM σ γ3) (b : β) (g : σ → Prop) (h : σ → σ)
    (l : γ3 → Int64) :
    FixLoop.mk.forIn b (fun _ _ => x1 >>= fun a1 => x2 a1 >>= fun a2 => x3 a2 >>= fun a3 =>
        (AInstr.exitIf g h (l a3) : BlockM σ (ForInStep β)))
      = x1 >>= fun a1 => x2 a1 >>= fun a2 => x3 a2 >>= fun a3 => AInstr.exitIf g h (l a3) := by
  rw [FixLoop.forIn_eq]
  simp only [bind_assoc, AInstr.exitIf_bind]

theorem forIn_bind5_exitIf {β : Type} {γ1 γ2 γ3 γ4 : Type} (x1 : BlockM σ γ1) (x2 : γ1 → BlockM σ γ2) (x3 : γ2 → BlockM σ γ3) (x4 : γ3 → BlockM σ γ4) (b : β) (g : σ → Prop) (h : σ → σ)
    (l : γ4 → Int64) :
    FixLoop.mk.forIn b (fun _ _ => x1 >>= fun a1 => x2 a1 >>= fun a2 => x3 a2 >>= fun a3 => x4 a3 >>= fun a4 =>
        (AInstr.exitIf g h (l a4) : BlockM σ (ForInStep β)))
      = x1 >>= fun a1 => x2 a1 >>= fun a2 => x3 a2 >>= fun a3 => x4 a3 >>= fun a4 => AInstr.exitIf g h (l a4) := by
  rw [FixLoop.forIn_eq]
  simp only [bind_assoc, AInstr.exitIf_bind]

theorem forIn_bind6_exitIf {β : Type} {γ1 γ2 γ3 γ4 γ5 : Type} (x1 : BlockM σ γ1) (x2 : γ1 → BlockM σ γ2) (x3 : γ2 → BlockM σ γ3) (x4 : γ3 → BlockM σ γ4) (x5 : γ4 → BlockM σ γ5) (b : β) (g : σ → Prop) (h : σ → σ)
    (l : γ5 → Int64) :
    FixLoop.mk.forIn b (fun _ _ => x1 >>= fun a1 => x2 a1 >>= fun a2 => x3 a2 >>= fun a3 => x4 a3 >>= fun a4 => x5 a4 >>= fun a5 =>
        (AInstr.exitIf g h (l a5) : BlockM σ (ForInStep β)))
      = x1 >>= fun a1 => x2 a1 >>= fun a2 => x3 a2 >>= fun a3 => x4 a3 >>= fun a4 => x5 a4 >>= fun a5 => AInstr.exitIf g h (l a5) := by
  rw [FixLoop.forIn_eq]
  simp only [bind_assoc, AInstr.exitIf_bind]

theorem forIn_exitIf {β : Type} (b : β) (g : σ → Prop) (h : σ → σ) (l : Int64) :
    FixLoop.mk.forIn b (fun _ _ => (AInstr.exitIf g h l : BlockM σ (ForInStep β))) = AInstr.exitIf g h l := by
  rw [FixLoop.forIn_eq, AInstr.exitIf_bind]

end

/-! ## Labels a block does not throw -/

section
variable {σ β : Type} {P : Int64 → σ → Prop}

theorem ThrowsOnly.modifyIf (g : σ → Prop) (f : σ → σ) :
    ThrowsOnly P (AInstr.modifyIf g f) = True := eq_true <| by
  intro Q E s hw
  simpa only [AInstr.wp_modifyIf] using hw

theorem ThrowsOnly.peek (c : σ → β) : ThrowsOnly P (AInstr.peek c : BlockM σ β) = True := eq_true <| by
  intro Q E s hw
  simpa only [AInstr.wp_peek] using hw

theorem ThrowsOnly.exitIf (g : σ → Prop) (f : σ → σ) {l : Int64} (hl : ∀ s, g s → P l (f s)) :
    ThrowsOnly P (AInstr.exitIf g f l : BlockM σ β) = True := eq_true <| by
  intro Q E s hw
  simp only [AInstr.wp_exitIf] at hw ⊢
  exact ⟨hw.1, hl s hw.1, hw.2⟩

theorem ThrowsOnly.branch (st c : σ → Bool) {l : Int64} (hl : ∀ s, st s = true → P l s) :
    ThrowsOnly P (AInstr.branch st c l) = True := eq_true <| by
  intro Q E s hw
  rw [AInstr.wp_branch] at hw ⊢
  by_cases hc : c s = true
  · simp only [hc, ↓reduceIte] at hw ⊢
    exact ⟨hw.1, hl s hw.1, hw.2⟩
  · simp only [hc, ↓reduceIte, Bool.false_eq_true] at hw ⊢
    exact hw

end

/-! ## Deciding labels and tables -/

theorem Table.get_cons {κ β : Type} [DecidableEq κ] [Inhabited β] (k k' : κ) (b : β)
    (t : Table κ β) : Table.get ((k', b) :: t) k = if k = k' then b else Table.get t k := by
  simp only [Table.get, List.lookup]
  by_cases h : k = k'
  · simp [h]
  · have hb : (k == k') = false := by simpa using h
    simp [h, hb]

theorem Program.label_eq_false [Host] {p : Program} [Embeds p] (hs : Program.Separated p = true)
    {l l' : Label} (hl : l ∈ Program.labels p) (hl' : l' ∈ Program.labels p) (hne : l ≠ l') :
    (label l = label l') = False :=
  eq_false (Program.label_ne_of_separated hs hl hl' hne)

theorem stayIn_setReg64_rsp (r₀ k : BitVec 64) (st : MachineData) :
    stayIn r₀ (AInstr.setReg64 .rsp (fun _ => r₀ + k) st) = !(BitVec.slt 0#64 k) := by
  rw [AInstr.setReg64, stayIn_setReg_rsp]
  congr 2
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

end Ascent.Kraken
