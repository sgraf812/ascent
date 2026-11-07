import Ascent.UB.WhileLoop
import Ascent.WPMonadExact
import Init.Internal.Order.MonadTail
import Std.WP.Triple.SpecLemmas

/-!
# Loops as least fixed points

`FixLoop` is the collection of a loop that runs until its body breaks. Its `ForIn` instance is the
least fixed point of one iteration, so `do` notation with `let mut`, `break` and `continue` works
over it as over `Lean.Loop`, and fixpoint induction applies to the loop. The macros `repeat'` and
`while'` are `repeat` and `while` over `FixLoop`:

```
do
  let mut i := 0
  while' i < n do
    i := i + 1
```

elaborates to `forIn FixLoop.mk 0 fun _ i => if i < n then … pure (.yield (i + 1)) else pure (.done i)`.
`FixLoop.forIn_eq` unfolds one iteration, as `Lean.Loop.forIn_eq_of_monadTail` does for `repeat`.
`FixLoop.Spec.forIn_fixLoop` is the `vcgen` specification of the loop, with an invariant and a
measure as for `repeat`.
-/

open Lean.Order Std.WP

namespace Ascent

instance : MonadTail UB := inferInstanceAs (MonadTail Option)

/-- The collection of a loop that runs until its body breaks. -/
structure FixLoop where

namespace FixLoop

section
variable {m : Type u → Type v} [Monad m] [MonadTail m] {β : Type u}

/-- One iteration of the loop: run the body, continue by `recur` on `yield`, stop on `done`. -/
def step (f : Unit → β → m (ForInStep β)) (recur : β → m β) (b : β) : m β := do
  match ← f () b with
  | .done b' => pure b'
  | .yield b' => recur b'

theorem step_monotone [Nonempty β] (f : Unit → β → m (ForInStep β)) : monotone (step f) :=
  fun _ _ h _ => MonadTail.bind_mono_right fun
    | .done _ => PartialOrder.rel_refl
    | .yield b' => h b'

/-- The loop, as the least fixed point of `step f`. -/
noncomputable def forIn (_ : FixLoop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  haveI : Nonempty β := ⟨init⟩
  fix (step f) (step_monotone f) init

noncomputable instance : ForIn m FixLoop Unit where
  forIn := FixLoop.forIn

theorem forIn_eq_forIn (l : FixLoop) (b : β) (f : Unit → β → m (ForInStep β)) :
    ForIn.forIn l b f = l.forIn b f := rfl

theorem forIn_eq (l : FixLoop) (b : β) (f : Unit → β → m (ForInStep β)) :
    l.forIn b f = (do
      match ← f () b with
      | .done val => pure val
      | .yield val => l.forIn val f) := by
  haveI : Nonempty β := ⟨b⟩
  show fix (step f) _ b = _
  rw [fix_eq (step_monotone f)]
  rfl

/-- Fixpoint induction: an admissible property of the loop function that every iteration preserves
holds of the loop. -/
theorem forIn_induct [Nonempty β] (f : Unit → β → m (ForInStep β)) (motive : (β → m β) → Prop)
    (hadm : admissible motive) (h : ∀ g, motive g → motive (step f g)) :
    motive fun b => FixLoop.mk.forIn b f := by
  show motive (fix (step f) (step_monotone f))
  exact fix_induct (step_monotone f) motive hadm h

end

section
variable {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'} [Monad m] [MonadTail m]
  [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m Pred EPosts]
  {β : Type u}

theorem wp_forIn_eq (l : FixLoop) (b : β) (f : Unit → β → m (ForInStep β)) (Q : β → Pred)
    (E : EPosts) :
    wp (l.forIn b f) Q E = wp (f () b) (fun r => match r with
      | .done val => Q val
      | .yield val => wp (l.forIn val f) Q E) E := by
  rw [forIn_eq, WPMonadExact.wp_bind_eq]
  congr 1
  funext r
  cases r <;> simp only [WPMonadExact.wp_pure_eq]

end

section
variable {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'} [Monad m] [MonadTail m]
  [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] {β : Type u}

@[spec]
theorem Spec.forIn_fixLoop [∀ P : Pred, PreservesSup (meet P)] {l : FixLoop} {init : β}
    {f : Unit → β → m (ForInStep β)} (measure : Variant β Pred) (inv : WhileInvariant β Pred)
    (einv : EPosts)
    (step : ∀ b (mb : measure.γ),
      Triple (f () b) (measure.EvalsTo b mb ⊓ inv false b)
        (fun r => match r with
          | .yield b' => measure.EvalsBelow b' mb ⊓ inv false b'
          | .done b' => inv true b')
        einv) :
    Triple (l.forIn init f) (inv false init) (fun b => inv true b) einv := by
  refine Triple.intro <| measure.le_of_total_le init ?_
  refine iSup_le _ _ fun minit => ?_
  suffices key : ∀ (n : measure.γ), Acc measure.rel n → ∀ b,
      Triple (l.forIn b f) (measure.EvalsTo b n ⊓ inv false b) (fun b => inv true b) einv
    from (key minit (measure.wf.apply minit) init).le_wp
  intro n hacc
  induction hacc with
  | intro n _ ih =>
    intro b
    rw [forIn_eq]
    refine Triple.bind (f := fun r => match r with
      | .done val => Pure.pure val
      | .yield val => l.forIn val f)
      (f () b) (fun r => match r with
        | .yield b' => measure.EvalsBelow b' n ⊓ inv false b'
        | .done b' => inv true b')
      (step b n) ?_
    rintro (b' | b')
    · exact Triple.pure b' PartialOrder.rel_refl
    · refine Triple.intro ?_
      refine iSup_meet_le fun mb' => ?_
      rw [meet_comm (P := measure.EvalsTo b' mb'), meet_assoc]
      exact CompleteLattice.ofProp_meet_le fun hlt => (ih mb' hlt b').le_wp

end

end FixLoop

/-- `repeat'` is `repeat` over `FixLoop`. -/
syntax "repeat' " doSeq : doElem
/-- `while'` is `while` over `FixLoop`. -/
syntax "while' " termBeforeDo " do " doSeq : doElem

macro_rules
  | `(doElem| repeat' $seq) => `(doElem| for _ in FixLoop.mk do $seq)
macro_rules
  | `(doElem| while' $c do $seq) => `(doElem| repeat' if $c then $seq else break)

end Ascent
