import Demo.L1
import Ascent.FixLoop

/-!
# From the block loop to a structured loop

`wp_cfgLoop_rotated` turns the block loop of a rotated loop into a `repeat'` loop. A rotated loop is
the shape a compiler emits for `while`: the entry block tests the exit condition `c₀` once and falls
into the loop block, the loop block jumps back to itself while `c` holds and falls out otherwise, and
the exit block ends the function:

```
cfgLoop (Table.get [(.entry, branch c₀ (.label X) >>= fun _ => e),
  (.label L, b >>= fun _ => branch c (.label L)), (.label X, x)]) next .entry
```

refines `rotated c₀ c e b x`:

```
do
  if c₀ (← get) then x
  else
    e
    repeat'
      b
      if !(c (← get)) then break
    x
```

The blocks `e` and `b` throw no label, and `x` throws only `.exit`. The `repeat'` loop is a least
fixed point, so the proof is fixpoint induction over it and needs no termination measure.
-/

open Std.WP Lean.Order Ascent

namespace Ascent.Kraken

section
variable {σ α : Type}

/-- The block program `x` ends normally or in undefined behaviour, never by a jump. -/
class NoThrow (x : BlockM σ α) : Prop where
  noThrow : ∀ s l s', x.run.run s ≠ some (.error l, s')

/-- The only label the block program `x` throws is `.exit`. -/
class Exits (x : BlockM σ α) : Prop where
  exits : ∀ s l s', x.run.run s = some (.error l, s') → l = .exit

theorem wp_get_bind (k : σ → BlockM σ α) (Q : α → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩)
    (s : σ) : wp (get >>= k) Q E s = wp (k s) Q E s := by
  rw [wp_BlockM_eq, wp_BlockM_eq]
  rfl

theorem wp_get (Q : σ → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (get : BlockM σ σ) Q E s = Q s s := by
  rw [wp_BlockM_eq]
  rfl

theorem NoThrow.wp_epost {x : BlockM σ α} (h : NoThrow x) {Q : α → σ → Prop}
    {E E' : (CfgLabel → σ → Prop) × EStack⟨⟩} {s : σ} : wp x Q E s → wp x Q E' s := by
  rw [wp_BlockM_eq, wp_BlockM_eq]
  rcases hr : x.run.run s with _ | ⟨l | _, s'⟩
  · exact id
  · exact (h.noThrow s l s' hr).elim
  · exact id

theorem Exits.wp_epost {x : BlockM σ α} (h : Exits x) {Q : α → σ → Prop}
    {E E' : (CfgLabel → σ → Prop) × EStack⟨⟩} (hE : ∀ s', E.1 .exit s' → E'.1 .exit s') {s : σ} :
    wp x Q E s → wp x Q E' s := by
  rw [wp_BlockM_eq, wp_BlockM_eq]
  rcases hr : x.run.run s with _ | ⟨l | _, s'⟩
  · exact id
  · rw [h.exits s l s' hr]; exact hE s'
  · exact id

/-- A property `wp u Q E s → R` of a block program is admissible. -/
theorem admissible_wp_imp (Q : α → σ → Prop) (E : (CfgLabel → σ → Prop) × EStack⟨⟩) (s : σ)
    (R : Prop) : admissible fun u : BlockM σ α => wp u Q E s → R := by
  intro ch hch hall hw
  have := WPCont.wp_csup (Prog := BlockM σ α) hch Q E s hw
  simp only [iSup_apply, iSup_prop_eq_exists] at this
  obtain ⟨⟨u, hu⟩, hwu⟩ := this
  exact hall u hu hwu

end

/-- The structured form of a rotated loop. -/
noncomputable def rotated {σ : Type} (c₀ c : σ → Bool) (e b x : BlockM σ Unit) : BlockM σ Unit := do
  if c₀ (← get) then x
  else
    e
    repeat'
      b
      if !(c (← get)) then break
    x

section
variable {σ : Type} {c₀ c : σ → Bool} {e b x : BlockM σ Unit} {L X : Label}
  {next : CfgLabel → CfgLabel} (Qa : Unit → σ → Prop) (Ea : (CfgLabel → σ → Prop) × EStack⟨⟩)

theorem wp_cfgLoop_rotated (hLX : L ≠ X) (he : NoThrow e) (hb : NoThrow b) (hx : Exits x)
    (hn₀ : next .entry = .label L) (hn₂ : next (.label L) = .label X)
    (hn₃ : next (.label X) = .exit) (s : σ) (h : wp (rotated c₀ c e b x) Qa Ea s) :
    wp (cfgLoop (Table.get [(.entry, AInstr.branch c₀ (.label X) >>= fun _ => e),
      (.label L, b >>= fun _ => AInstr.branch c (.label L)), (.label X, x)]) next .entry) Qa Ea s := by
  have hXL : X ≠ L := Ne.symm hLX
  have b₁ : (CfgLabel.label L == CfgLabel.entry) = false := by simp
  have b₂ : (CfgLabel.label L == CfgLabel.label L) = true := by simp
  have b₃ : (CfgLabel.label X == CfgLabel.entry) = false := by simp
  have b₄ : (CfgLabel.label X == CfgLabel.label L) = false := by simp [hXL]
  have b₅ : (CfgLabel.label X == CfgLabel.label X) = true := by simp
  have hget₀ : Table.get [(CfgLabel.entry, AInstr.branch c₀ (.label X) >>= fun _ => e),
      (.label L, b >>= fun _ => AInstr.branch c (.label L)), (.label X, x)] .entry
      = AInstr.branch c₀ (.label X) >>= fun _ => e := by simp [Table.get, List.lookup]
  have hget₂ : Table.get [(CfgLabel.entry, AInstr.branch c₀ (.label X) >>= fun _ => e),
      (.label L, b >>= fun _ => AInstr.branch c (.label L)), (.label X, x)] (.label L)
      = b >>= fun _ => AInstr.branch c (.label L) := by
    simp only [Table.get, List.lookup, b₁, b₂, Option.getD_some]
  have hget₃ : Table.get [(CfgLabel.entry, AInstr.branch c₀ (.label X) >>= fun _ => e),
      (.label L, b >>= fun _ => AInstr.branch c (.label L)), (.label X, x)] (.label X) = x := by
    simp only [Table.get, List.lookup, b₃, b₄, b₅, Option.getD_some]
  generalize htbl : Table.get [(CfgLabel.entry, AInstr.branch c₀ (.label X) >>= fun _ => e),
      (.label L, b >>= fun _ => AInstr.branch c (.label L)), (.label X, x)] = tbl at hget₀ hget₂ hget₃ ⊢
  -- The exit block ends the run.
  have hX : ∀ s, wp x Qa Ea s → wp (cfgLoop tbl next (.label X)) Qa Ea s := by
    intro s hw
    rw [wp_cfgLoop _ _ _ _ _ (by simp), hget₃, hn₃, wp_cfgLoop_exit_fn]
    exact Exits.wp_epost hx (fun s' h' => by simp only [cfgEPosts_exit]; exact h') hw
  -- The loop block, by fixpoint induction over the `repeat'` loop.
  let f : Unit → PUnit → BlockM σ (ForInStep PUnit) := fun _ _ => do
    b
    let d ← get
    if (!c d) = true then pure (ForInStep.done PUnit.unit) else pure (ForInStep.yield PUnit.unit)
  have hL : ∀ s, wp (FixLoop.mk.forIn PUnit.unit f) (fun _ => wp x Qa Ea) Ea s →
      wp (cfgLoop tbl next (.label L)) Qa Ea s := by
    have := FixLoop.forIn_induct f
      (fun g => ∀ s, wp (g PUnit.unit) (fun _ => wp x Qa Ea) Ea s →
        wp (cfgLoop tbl next (.label L)) Qa Ea s)
      (admissible_pi _ fun s =>
        admissible_apply (fun _ u => wp u (fun _ => wp x Qa Ea) Ea s →
          wp (cfgLoop tbl next (.label L)) Qa Ea s) PUnit.unit
          (admissible_wp_imp _ Ea s _)) ?_
    · exact this
    intro g ih s hw
    simp only [FixLoop.step, f, WPMonadExact.wp_bind_eq] at hw
    rw [wp_cfgLoop _ _ _ _ _ (by simp), hget₂, hn₂, WPMonadExact.wp_bind_eq]
    refine NoThrow.wp_epost hb (E := Ea) ?_
    refine WP.wp_monotone_post (x := b) (fun _ st hst => ?_) s hw
    rw [wp_get] at hst
    rw [AInstr.wp_branch]
    cases hc : c st
    · simp only [hc, Bool.not_false, ↓reduceIte, WPMonadExact.wp_pure_eq, Bool.false_eq_true] at hst ⊢
      exact hX st hst
    · simp only [hc, Bool.not_true, ↓reduceIte, WPMonadExact.wp_pure_eq, Bool.false_eq_true] at hst ⊢
      simp only [cfgEPosts_label]
      exact ih st hst
  -- The entry block.
  unfold rotated at h
  rw [wp_get_bind] at h
  rw [wp_cfgLoop _ _ _ _ _ (by simp), hget₀, WPMonadExact.wp_bind_eq, AInstr.wp_branch]
  cases hc₀ : c₀ s
  · simp only [hc₀, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [WPMonadExact.wp_bind_eq] at h
    rw [hn₀]
    refine NoThrow.wp_epost he (E := Ea) ?_
    refine WP.wp_monotone_post (x := e) (fun _ st hst => ?_) s h
    rw [WPMonadExact.wp_bind_eq] at hst
    exact hL st hst
  · simp only [hc₀, ↓reduceIte] at h ⊢
    simp only [cfgEPosts_label]
    exact hX s h

end

/-- `wp_cfgLoop_rotated` as a refinement: the rotated block loop refines its structured form under
the identity view, with the thrown labels related by equality. The entry block is the continuation
`e` of the exit test, so that its instance `NoThrow (e ())` is found once the rule has matched. -/
theorem refines_cfgLoop_rotated {σ : Type} {c₀ c : σ → Bool} {e : Unit → BlockM σ Unit}
    {b x : BlockM σ Unit} {L X : Label} {next : CfgLabel → CfgLabel} [he : NoThrow (e ())]
    [hb : NoThrow b] [hx : Exits x] (hLX : L ≠ X)
    (hn₀ : next .entry = .label L) (hn₂ : next (.label L) = .label X)
    (hn₃ : next (.label X) = .exit) :
    ⦃(⊤ : σ → Prop)⦄
      (cfgLoop (Table.get [(.entry, AInstr.branch c₀ (.label X) >>= e),
        (.label L, b >>= fun _ => AInstr.branch c (.label L)), (.label X, x)]) next .entry)
      ⪯[Concretization.ofStateRepr id] (rotated c₀ c (e ()) b x)
      ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred, id] at hs
  refine wp_cfgLoop_rotated (e := e ()) _ _ hLX he hb hx hn₀ hn₂ hn₃ s ?_
  refine WP.wp_monotone (x := rotated c₀ c (e ()) b x) ?_ ?_ s hs.2
  · intro u s' hq
    rw [Concretization.post_pi]
    exact ⟨u, trivial, hq⟩
  · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l s' hq
    simp only [EPostsConcretization.ePosts_cons]
    rw [Concretization.post_pi]
    exact ⟨l, rfl, hq⟩

end Ascent.Kraken
