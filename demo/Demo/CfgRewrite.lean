import Demo.L1
import Ascent.FixLoop
import Ascent.FixLoop.Delab

/-!
# Structuring a block loop by rewriting

The block loop of a text is structured by `cfgLoop_header` of `Ascent.BlockLoop`, applied at every
label: each label becomes the header of a `repeat'` loop over the other blocks that continues on a
return to the label. The equations of this file push the loop's `try` into the blocks, through a
mapped computation as well, until it meets the literal labels of the throws; a throw of the header
continues, any other label is thrown on. A handler crosses an inner loop that never throws its label
(`tryCatch_forIn_bind`, with the exception effect `ThrowsOnly` as premise). The marks `done <$>` then
collect at the root of a body (`pure_done_eq`, `bind_map`, `condState_map`, `throw_label_step`),
an exit absorbs a mark (`map_exitIf`, `map_bind_exitIf`), and a loop whose body never continues
collapses to its body (`forIn_map_done`, `forIn_bind_exitIf`, `forIn_exitIf`).
-/

open Std.WP Lean.Order Ascent

namespace Ascent.Kraken

theorem BlockM.ext_wp {σ α : Type} {x y : BlockM σ α}
    (h : ∀ (Q : α → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩) s, wp x Q E s → wp y Q E s)
    (h' : ∀ (Q : α → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩) s, wp y Q E s → wp x Q E s) :
    x = y :=
  BlockLoop.ext_wp h h'

/-! ## Pushing `try` into a block -/

section
variable {σ β : Type}

theorem tryCatch_bind_assoc {α γ : Type} (x : BlockM σ α) (f : α → BlockM σ γ) (k : γ → BlockM σ β)
    (h : CfgLabel → BlockM σ β) :
    tryCatch ((x >>= f) >>= k) h = tryCatch (x >>= fun a => f a >>= k) h := by
  rw [bind_assoc]

theorem tryCatch_pure (b : β) (h : CfgLabel → BlockM σ β) : tryCatch (pure b : BlockM σ β) h = pure b := by
  apply BlockM.ext_wp <;> intro Q E s <;> simp only [wp_tryCatch_block, WPMonadExact.wp_pure_eq] <;>
    exact id

theorem tryCatch_modifyIf_bind (g : σ → Prop) (f : σ → σ) (k : Unit → BlockM σ β)
    (h : CfgLabel → BlockM σ β) :
    tryCatch (AInstr.modifyIf g f >>= k) h = AInstr.modifyIf g f >>= fun a => tryCatch (k a) h := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [wp_tryCatch_block, WPMonadExact.wp_bind_eq, AInstr.wp_modifyIf] <;> exact id

theorem tryCatch_peek_bind {γ : Type} (c : σ → γ) (k : γ → BlockM σ β) (h : CfgLabel → BlockM σ β) :
    tryCatch (AInstr.peek c >>= k) h = AInstr.peek c >>= fun z => tryCatch (k z) h := rfl

theorem tryCatch_exitIf_bind (g : σ → Prop) (f : σ → σ) (l : CfgLabel) (k : Unit → BlockM σ β)
    (h : CfgLabel → BlockM σ β) (hh : h l = throw l) :
    tryCatch (AInstr.exitIf g f l >>= k) h = AInstr.exitIf g f l >>= k := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [wp_tryCatch_block, WPMonadExact.wp_bind_eq, AInstr.wp_exitIf, hh, wp_throw_block] <;>
    exact id

def condState (c : σ → Bool) (x y : BlockM σ β) : BlockM σ β :=
  get >>= fun st => if c st then x else y

theorem wp_condState (c : σ → Bool) (x y : BlockM σ β) (Q : β → σ → Prop)
    (E : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (condState c x y) Q E s = if c s then wp x Q E s else wp y Q E s := by
  rw [condState, wp_get_bind]
  split <;> rfl

theorem condState_const (b : Bool) (x y : BlockM σ β) :
    condState (fun _ => b) x y = if b = true then x else y := by
  cases b <;> apply BlockM.ext_wp <;> intro Q E s <;> simp [wp_condState]

theorem condState_true (x y : BlockM σ β) : condState (fun _ => true) x y = x := rfl

theorem condState_false (x y : BlockM σ β) : condState (fun _ => false) x y = y := rfl

theorem modifyIf_true_bind_condState (f : σ → σ) (c : σ → Bool) (x y : BlockM σ β) :
    (AInstr.modifyIf (fun _ => True) f >>= fun _ => condState c x y)
      = condState (fun st => c (f st)) (AInstr.modifyIf (fun _ => True) f >>= fun _ => x)
          (AInstr.modifyIf (fun _ => True) f >>= fun _ => y) := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [WPMonadExact.wp_bind_eq, AInstr.wp_modifyIf, wp_condState] <;> split <;> simp_all

theorem tryCatch_condState (c : σ → Bool) (x y : BlockM σ β) (h : CfgLabel → BlockM σ β) :
    tryCatch (condState c x y) h = condState c (tryCatch x h) (tryCatch y h) := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [wp_tryCatch_block, wp_condState] <;> split <;> exact id

theorem tryCatch_condState_bind {γ : Type} (c : σ → Bool) (x y : BlockM σ γ) (k : γ → BlockM σ β)
    (h : CfgLabel → BlockM σ β) :
    tryCatch (condState c x y >>= k) h = condState c (tryCatch (x >>= k) h) (tryCatch (y >>= k) h) := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [wp_tryCatch_block, WPMonadExact.wp_bind_eq, wp_condState] <;> split <;> exact id

theorem tryCatch_branch_bind (c : σ → Bool) (l : CfgLabel) (k : Unit → BlockM σ β)
    (h : CfgLabel → BlockM σ β) :
    tryCatch (AInstr.branch c l >>= k) h = condState c (h l) (tryCatch (k ()) h) := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [wp_tryCatch_block, WPMonadExact.wp_bind_eq, AInstr.wp_branch, wp_condState] <;>
    split <;> exact id

theorem tryCatch_exitIf {α : Type} (g : σ → Prop) (f : σ → σ) (l : CfgLabel) (h : CfgLabel → BlockM σ α)
    (hh : h l = throw l) : tryCatch (AInstr.exitIf g f l : BlockM σ α) h = AInstr.exitIf g f l := by
  apply BlockM.ext_wp <;> intro Q E s <;>
    simp only [wp_tryCatch_block, AInstr.wp_exitIf, hh, wp_throw_block] <;> exact id

theorem pure_done_eq (u : PUnit) :
    (pure (ForInStep.done u) : BlockM σ (ForInStep PUnit)) = ForInStep.done <$> (pure u : BlockM σ PUnit) :=
  (map_pure _ _).symm

theorem bind_map {α γ δ : Type} (x : BlockM σ α) (y : α → BlockM σ γ) (f : γ → δ) :
    (x >>= fun a => f <$> y a) = f <$> (x >>= y) :=
  (map_bind _ _ _).symm

theorem condState_map {γ δ : Type} (c : σ → Bool) (f : γ → δ) (x y : BlockM σ γ) :
    condState c (f <$> x) (f <$> y) = f <$> condState c x y := by
  simp only [condState, map_bind]
  congr 1
  funext st
  split <;> rfl

theorem map_exitIf {γ δ : Type} (f : γ → δ) (g : σ → Prop) (h : σ → σ) (l : CfgLabel) :
    f <$> (AInstr.exitIf g h l : BlockM σ γ) = AInstr.exitIf g h l := by
  rw [map_eq_pure_bind, AInstr.exitIf_bind]

theorem tryCatch_map_bind {α γ δ : Type} (f : γ → δ) (x : BlockM σ α) (k : α → BlockM σ γ)
    (h : CfgLabel → BlockM σ δ) :
    tryCatch (f <$> (x >>= k)) h = tryCatch (x >>= fun a => f <$> k a) h := by
  rw [map_bind]

theorem tryCatch_map_condState {γ δ : Type} (f : γ → δ) (c : σ → Bool) (x y : BlockM σ γ)
    (h : CfgLabel → BlockM σ δ) :
    tryCatch (f <$> condState c x y) h = condState c (tryCatch (f <$> x) h) (tryCatch (f <$> y) h) := by
  rw [← condState_map, tryCatch_condState]

theorem tryCatch_map_throw {γ δ : Type} (f : γ → δ) (l : CfgLabel) (h : CfgLabel → BlockM σ δ) :
    tryCatch (f <$> (throw l : BlockM σ γ)) h = h l := by
  rw [map_eq_pure_bind, BlockLoop.throw_bind, BlockLoop.tryCatch_throw]

theorem tryCatch_map_exitIf {γ δ : Type} (f : γ → δ) (g : σ → Prop) (u : σ → σ) (l : CfgLabel)
    (h : CfgLabel → BlockM σ δ) (hh : h l = throw l) :
    tryCatch (f <$> (AInstr.exitIf g u l : BlockM σ γ)) h = f <$> (AInstr.exitIf g u l : BlockM σ γ) := by
  rw [map_exitIf, tryCatch_exitIf _ _ _ _ hh]

theorem tryCatch_map_pure {γ δ : Type} (f : γ → δ) (a : γ) (h : CfgLabel → BlockM σ δ) :
    tryCatch (f <$> (pure a : BlockM σ γ)) h = f <$> (pure a : BlockM σ γ) := by
  rw [map_pure, tryCatch_pure]

theorem tryCatch_map_modifyIf {δ : Type} (f : Unit → δ) (g : σ → Prop) (u : σ → σ)
    (h : CfgLabel → BlockM σ δ) :
    tryCatch (f <$> AInstr.modifyIf g u) h = f <$> AInstr.modifyIf g u := by
  rw [map_eq_pure_bind, ← bind_pure (AInstr.modifyIf g u >>= _), bind_assoc, tryCatch_modifyIf_bind]
  simp only [pure_bind, tryCatch_pure, bind_pure_comp]

theorem throw_label_step (s : Label) :
    (throw (CfgLabel.label s) : BlockM σ (ForInStep PUnit))
      = ForInStep.done <$> (throw (CfgLabel.label s) : BlockM σ PUnit) := by
  rw [map_eq_pure_bind, BlockLoop.throw_bind]

theorem condState_exitIf_map {γ δ : Type} (c : σ → Bool) (g : σ → Prop) (h : σ → σ) (l : CfgLabel)
    (f : γ → δ) (y : BlockM σ γ) :
    condState c (AInstr.exitIf g h l) (f <$> y) = f <$> condState c (AInstr.exitIf g h l) y := by
  rw [← condState_map, map_exitIf]

theorem condState_map_exitIf {γ δ : Type} (c : σ → Bool) (g : σ → Prop) (h : σ → σ) (l : CfgLabel)
    (f : γ → δ) (x : BlockM σ γ) :
    condState c (f <$> x) (AInstr.exitIf g h l) = f <$> condState c x (AInstr.exitIf g h l) := by
  rw [← condState_map, map_exitIf]

theorem forIn_map_done (x : BlockM σ PUnit) :
    FixLoop.mk.forIn PUnit.unit (fun _ _ => ForInStep.done <$> x) = x := by
  rw [FixLoop.forIn_eq, map_eq_pure_bind, bind_assoc]
  simp only [pure_bind]
  exact bind_pure_unit

theorem map_bind_exitIf {α γ δ : Type} (f : γ → δ) (x : BlockM σ α) (g : σ → Prop) (h : σ → σ)
    (l : CfgLabel) :
    f <$> (x >>= fun _ => (AInstr.exitIf g h l : BlockM σ γ)) = x >>= fun _ => AInstr.exitIf g h l := by
  rw [map_bind]
  simp only [map_exitIf]

theorem condState_bind_exitIf_map {α γ δ : Type} (c : σ → Bool) (x : BlockM σ α) (g : σ → Prop)
    (h : σ → σ) (l : CfgLabel) (f : γ → δ) (y : BlockM σ γ) :
    condState c (x >>= fun _ => AInstr.exitIf g h l) (f <$> y)
      = f <$> condState c (x >>= fun _ => AInstr.exitIf g h l) y := by
  rw [← condState_map, map_bind_exitIf]

theorem condState_map_bind_exitIf {α γ δ : Type} (c : σ → Bool) (x : BlockM σ α) (g : σ → Prop)
    (h : σ → σ) (l : CfgLabel) (f : γ → δ) (y : BlockM σ γ) :
    condState c (f <$> y) (x >>= fun _ => AInstr.exitIf g h l)
      = f <$> condState c y (x >>= fun _ => AInstr.exitIf g h l) := by
  rw [← condState_map, map_bind_exitIf]

theorem forIn_bind_exitIf {α β : Type} (b : β) (x : BlockM σ α) (g : σ → Prop) (h : σ → σ)
    (l : CfgLabel) :
    FixLoop.mk.forIn b (fun _ _ => x >>= fun _ => (AInstr.exitIf g h l : BlockM σ (ForInStep β)))
      = x >>= fun _ => AInstr.exitIf g h l := by
  rw [FixLoop.forIn_eq, bind_assoc]
  simp only [AInstr.exitIf_bind]

theorem forIn_bind_bind_exitIf {α γ β : Type} (b : β) (x : BlockM σ α) (y : BlockM σ γ) (g : σ → Prop)
    (h : σ → σ) (l : CfgLabel) :
    FixLoop.mk.forIn b (fun _ _ => x >>= fun _ => y >>= fun _ => (AInstr.exitIf g h l : BlockM σ (ForInStep β)))
      = x >>= fun _ => y >>= fun _ => AInstr.exitIf g h l := by
  rw [FixLoop.forIn_eq, bind_assoc]
  simp only [bind_assoc, AInstr.exitIf_bind]

theorem forIn_exitIf {β : Type} (b : β) (g : σ → Prop) (h : σ → σ) (l : CfgLabel) :
    FixLoop.mk.forIn b (fun _ _ => (AInstr.exitIf g h l : BlockM σ (ForInStep β))) = AInstr.exitIf g h l := by
  rw [FixLoop.forIn_eq, AInstr.exitIf_bind]

end

/-! ## Labels a block does not throw -/

section
variable {σ β : Type} {P : CfgLabel → Prop}

theorem ThrowsOnly.modifyIf (g : σ → Prop) (f : σ → σ) :
    ThrowsOnly P (AInstr.modifyIf g f) = True := eq_true <| by
  intro Q E s hw
  simpa only [AInstr.wp_modifyIf] using hw

theorem ThrowsOnly.peek (c : σ → β) : ThrowsOnly P (AInstr.peek c : BlockM σ β) = True := eq_true <| by
  intro Q E s hw
  simpa only [AInstr.wp_peek] using hw

theorem ThrowsOnly.exitIf (g : σ → Prop) (f : σ → σ) {l : CfgLabel} (hl : P l) :
    ThrowsOnly P (AInstr.exitIf g f l : BlockM σ β) = True := eq_true <| by
  intro Q E s hw
  simp only [AInstr.wp_exitIf] at hw ⊢
  exact ⟨hw.1, hl, hw.2⟩

theorem ThrowsOnly.branch (c : σ → Bool) {l : CfgLabel} (hl : P l) :
    ThrowsOnly P (AInstr.branch c l) = True := eq_true <| by
  intro Q E s hw
  rw [AInstr.wp_branch] at hw ⊢
  by_cases hc : c s = true
  · simp only [hc, ↓reduceIte] at hw ⊢
    exact ⟨hl, hw⟩
  · simp only [hc, ↓reduceIte, Bool.false_eq_true] at hw ⊢
    exact hw

theorem ThrowsOnly.condState (c : σ → Bool) {x y : BlockM σ β} (hx : ThrowsOnly P x)
    (hy : ThrowsOnly P y) : ThrowsOnly P (condState c x y) = True := eq_true <| by
  intro Q E s hw
  rw [wp_condState] at hw ⊢
  by_cases hc : c s = true
  · simp only [hc, ↓reduceIte] at hw ⊢
    exact hx _ _ s hw
  · simp only [hc, ↓reduceIte, Bool.false_eq_true] at hw ⊢
    exact hy _ _ s hw

end

/-! ## Deciding labels and tables -/

theorem Table.get_cons {κ β : Type} [DecidableEq κ] [Inhabited β] (k k' : κ) (b : β)
    (t : Table κ β) : Table.get ((k', b) :: t) k = if k = k' then b else Table.get t k := by
  simp only [Table.get, List.lookup]
  by_cases h : k = k'
  · simp [h]
  · have hb : (k == k') = false := by simpa using h
    simp [h, hb]

theorem CfgLabel.label_eq_label (a b : Label) : (CfgLabel.label a = CfgLabel.label b) = (@Eq String a b) := by
  simp

theorem tryCatch_table_get_bind {σ α β : Type} [Inhabited (BlockM σ α)] (k k' : CfgLabel) (c : BlockM σ α)
    (t : Table CfgLabel (BlockM σ α)) (K : α → BlockM σ β) (h : CfgLabel → BlockM σ β) :
    tryCatch (Table.get ((k', c) :: t) k >>= K) h
      = if k = k' then tryCatch (c >>= K) h else tryCatch (Table.get t k >>= K) h := by
  rw [Table.get_cons]
  split <;> rfl

end Ascent.Kraken
