import Std.Internal.Do

/-!
# `Corres`: soundness of monadic abstraction

`Corres r P αV a c` states that, under the concrete-state precondition `P`, the abstract program
`a` soundly abstracts the concrete program `c`: any property proved of `a` transports to `c` where
`P` holds. It is read as abstract interpretation,
`(P ⊓ r.γP (wp a Q E)) ⊑ wp c (r.γQ αV Q) (r.γE E)`.

`Refinement` carries the monad-level concretizations `γP`/`γE` (the AutoCorres state/exception
abstraction; `Refinement.ofStateRepr` builds the common functional case as a pullback). The value
abstraction `αV` is per-`Corres` (`bind` relates programs at different value types). The precondition
`P` is threaded by `corres_bind` (the AutoCorres `corresXF_split`), so a coupling that is *established*
mid-program (e.g. a loop counter) need not hold from the start.
-/

open Std.Internal.Do Lean.Order

namespace Ascent

universe u v w w'

/-- If `wp` lower-bounds the postcondition on `pure`, then with `WPMonad` it computes `pure`. -/
theorem wp_pure_eq {m : Type u → Type v} {Pred : Type w} {EPred : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (wp_pure_le : ∀ {α} (a : α) (post : α → Pred) (epost : EPred),
      wp (pure a : m α) post epost ⊑ post a)
    {α} (a : α) (post : α → Pred) (epost : EPred) :
    wp (pure a : m α) post epost = post a :=
  PartialOrder.rel_antisymm (wp_pure_le a post epost) (WPMonad.pure_le_wp_pure a post epost)

/-- If `wp` lower-bounds the decomposition on `bind`, then with `WPMonad` it computes `bind`. -/
theorem wp_bind_eq {m : Type u → Type v} {Pred : Type w} {EPred : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (wp_bind_le : ∀ {α β} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred),
      wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost)
    {α β} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost :=
  PartialOrder.rel_antisymm (wp_bind_le x f post epost) (WPMonad.bind_le_wp_bind x f post epost)

/-- A refinement between two `WP` setups: monad-level concretizations of normal and
exceptional assertions. The value-level abstraction is supplied per `Corres` statement. -/
structure Refinement (CPred : Type w) (APred : Type w) (CEPred : Type w') (AEPred : Type w')
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred] where
  /-- Concretization of normal assertions. -/
  γP : APred → CPred
  /-- Concretization of exceptional assertions. -/
  γE : AEPred → CEPred
  /-- `γP` is monotone. -/
  γP_mono : ∀ {p q : APred}, p ⊑ q → γP p ⊑ γP q
  /-- `γE` is monotone. -/
  γE_mono : ∀ {p q : AEPred}, p ⊑ q → γE p ⊑ γE q

namespace Refinement

variable {CPred APred : Type w} {CEPred AEPred : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]

/-- Postcondition concretization. The value coupling `αV av cv : CPred` relates an abstract value
`av` to a concrete value `cv`; being a `CPred`, it may depend on the concrete state, which is what
lets an out-parameter's final value be read off the exit state. For each concrete value the abstract
postcondition is reified against the coupling and concretized. -/
noncomputable def γQ (r : Refinement CPred APred CEPred AEPred) {CVal AVal : Type _}
    (αV : AVal → CVal → CPred) (Q : AVal → APred) : CVal → CPred :=
  fun cv => iSup fun av => αV av cv ⊓ r.γP (Q av)

end Refinement

/-- The functional value coupling: the abstract value is exactly `f cv`. Recovers the
state-independent value abstraction. -/
noncomputable def αVeq {CVal AVal : Type _} {CPred : Type w} [Assertion CPred] (f : CVal → AVal) :
    AVal → CVal → CPred := fun av cv => ⌜av = f cv⌝

namespace Refinement

variable {CPred APred : Type w} {CEPred AEPred : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]

/-- One-point rule: under the functional coupling the reified `iSup` collapses to the pullback. -/
@[simp] theorem γQ_αVeq (r : Refinement CPred APred CEPred AEPred) {CVal AVal : Type _}
    (f : CVal → AVal) (Q : AVal → APred) :
    r.γQ (αVeq f) Q = fun cv => r.γP (Q (f cv)) := by
  funext cv
  refine PartialOrder.rel_antisymm (iSup_le _ _ fun av => ?_) ?_
  · show (⌜av = f cv⌝ : CPred) ⊓ r.γP (Q av) ⊑ r.γP (Q (f cv))
    exact CompleteLattice.ofProp_meet_le_left (by rintro rfl; exact PartialOrder.rel_refl)
  · refine PartialOrder.rel_trans ?_ (le_iSup (fun av => αVeq f av cv ⊓ r.γP (Q av)) (f cv))
    exact le_meet _ _ _ (le_ofProp _ _ rfl) PartialOrder.rel_refl

/-- The functional refinement from a state representation function `st : Cσ → Aσ`: the
concretization is the pullback `st^*` (`γP P = P ∘ st`). Exception-free (`EPost.Nil`). This is
AutoCorres' functional state abstraction; the coupling side-condition lives in the `Corres`
precondition `P`, not here. -/
def ofStateRepr {Cσ Aσ : Type w} (st : Cσ → Aσ) :
    Refinement (Cσ → Prop) (Aσ → Prop) EPost.Nil EPost.Nil where
  γP P := fun cs => P (st cs)
  γE := id
  γP_mono h := fun cs => h (st cs)
  γE_mono h := h

@[simp] theorem ofStateRepr_γP {Cσ Aσ : Type w} (st : Cσ → Aσ) (P : Aσ → Prop) :
    (ofStateRepr st).γP P = fun cs => P (st cs) := rfl

@[simp] theorem ofStateRepr_γQ {Cσ Aσ CV AV : Type w} (st : Cσ → Aσ) (f : CV → AV)
    (Q : AV → Aσ → Prop) : (ofStateRepr st).γQ (αVeq f) Q = fun cv cs => Q (f cv) (st cs) := by
  simp only [γQ_αVeq, ofStateRepr_γP]

end Refinement

/-- The abstract program `a` soundly abstracts the concrete program `c` under refinement `r`,
value abstraction `αV`, and concrete-state precondition `P`. -/
def Corres {CProg AProg : Type _} {CVal AVal : Type _}
    {CPred APred : Type w} {CEPred AEPred : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
    [WP CProg CVal CPred CEPred] [WP AProg AVal APred AEPred]
    (r : Refinement CPred APred CEPred AEPred) (P : CPred) (αV : AVal → CVal → CPred)
    (a : AProg) (c : CProg) : Prop :=
  ∀ Q E, (P ⊓ r.γP (wp a Q E)) ⊑ wp c (r.γQ αV Q) (r.γE E)

/-! ## Structural laws -/

section Structural

variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPred AEPred : Type w'}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WPMonad CM CPred CEPred] [WPMonad AM APred AEPred]

/-- The facts that make a refinement lawful: the abstract `wp` lower-bounds `pure`/`bind`, i.e. it
is a monad morphism. -/
class LawfulRefinement (_r : Refinement CPred APred CEPred AEPred)
    (CM AM : Type w → Type v) [Monad CM] [Monad AM]
    [WPMonad CM CPred CEPred] [WPMonad AM APred AEPred] : Prop where
  /-- Abstract `wp` lower-bounds `pure`. -/
  wp_pure_le {α : Type w} (a : α) (post : α → APred) (epost : AEPred) :
    wp (pure a : AM α) post epost ⊑ post a
  /-- Abstract `wp` lower-bounds the `bind` decomposition. -/
  wp_bind_le {α β : Type w} (x : AM α) (f : α → AM β) (post : β → APred) (epost : AEPred) :
    wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost

/-- The concrete `wp` is conjunctive. Needed only by the precondition-threading `corres_bind` (not
`corres_bind_top`); every deterministic / demonic monad satisfies it. -/
class ConjWP (CM : Type w → Type v) (CPred : Type w) (CEPred : Type w')
    [Monad CM] [Assertion CPred] [Assertion CEPred] [WPMonad CM CPred CEPred] : Prop where
  /-- Concrete `wp` distributes over meets of postconditions. -/
  wp_meet {α : Type w} (x : CM α) (A B : α → CPred) (E : CEPred) :
    wp x A E ⊓ wp x B E ⊑ wp x (fun v => A v ⊓ B v) E

variable {r : Refinement CPred APred CEPred AEPred} [LawfulRefinement r CM AM]

/-- `pure` abstracts `pure` when the returned values correspond (precondition-agnostic). -/
theorem corres_pure {CVal AVal : Type w} (P : CPred) (αV : CVal → AVal) {a : AVal} {c : CVal}
    (h : αV c = a) : Corres r P (αVeq αV) (pure a : AM AVal) (pure c : CM CVal) := by
  intro Q E
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  refine PartialOrder.rel_trans (r.γP_mono ((‹LawfulRefinement r CM AM›).wp_pure_le a Q E)) ?_
  have hQ : r.γQ (αVeq αV) Q c = r.γP (Q a) := by simp [Refinement.γQ_αVeq, h]
  rw [← hQ]
  exact WPMonad.pure_le_wp_pure c (r.γQ (αVeq αV) Q) (r.γE E)

/-- `bind` abstracts `bind`, threading the precondition (`corresXF_split`): the heads correspond
under `P`, the concrete head establishes the mid-coupling `R`, and the continuations correspond
under `R`. -/
theorem corres_bind [ConjWP CM CPred CEPred] {CV AV CV₂ AV₂ : Type w} (P : CPred) (R : CV → CPred)
    (αV : CV → AV) (αV₂ : CV₂ → AV₂)
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    (hc : Corres r P (αVeq αV) a₁ c₁)
    (hmid : ∀ E, P ⊑ wp c₁ (fun cv => R cv) E)
    (hf : ∀ cv, Corres r (R cv) (αVeq αV₂) (a₂ (αV cv)) (c₂ cv)) :
    Corres r P (αVeq αV₂) (a₁ >>= a₂) (c₁ >>= c₂) := by
  intro Q E
  have step1 : (P ⊓ r.γP (wp (a₁ >>= a₂) Q E)) ⊑ (P ⊓ r.γP (wp a₁ (fun av => wp (a₂ av) Q E) E)) :=
    le_meet _ _ _ (meet_le_left _ _)
      (PartialOrder.rel_trans (meet_le_right _ _) (r.γP_mono ((‹LawfulRefinement r CM AM›).wp_bind_le a₁ a₂ Q E)))
  refine PartialOrder.rel_trans step1 ?_
  have hi := hc (fun av => wp (a₂ av) Q E) E
  have hii : (P ⊓ r.γP (wp a₁ (fun av => wp (a₂ av) Q E) E)) ⊑ wp c₁ (fun cv => R cv) (r.γE E) :=
    PartialOrder.rel_trans (meet_le_left _ _) (hmid (r.γE E))
  refine PartialOrder.rel_trans (le_meet _ _ _ hi hii) ?_
  refine PartialOrder.rel_trans ((‹ConjWP CM CPred CEPred›).wp_meet c₁ (r.γQ (αVeq αV) (fun av => wp (a₂ av) Q E))
    (fun cv => R cv) (r.γE E)) ?_
  refine PartialOrder.rel_trans
    (WP.wp_consequence c₁ _ (fun cv => wp (c₂ cv) (r.γQ (αVeq αV₂) Q) (r.γE E)) (r.γE E) ?_) ?_
  · intro cv
    simp only [Refinement.γQ_αVeq]
    have hfcv := hf cv Q E
    simp only [Refinement.γQ_αVeq] at hfcv
    refine PartialOrder.rel_trans ?_ hfcv
    exact le_meet _ _ _ (meet_le_right _ _) (meet_le_left _ _)
  · exact WPMonad.bind_le_wp_bind c₁ c₂ (r.γQ (αVeq αV₂) Q) (r.γE E)

/-- The precondition-free `bind`: when no mid-coupling is needed (`P = ⊤`, `R = ⊤`), neither `hmid`
nor conjunctivity is used. -/
theorem corres_bind_top {CV AV CV₂ AV₂ : Type w} (αV : CV → AV) (αV₂ : CV₂ → AV₂)
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    (hc : Corres r ⊤ (αVeq αV) a₁ c₁) (hf : ∀ cv, Corres r ⊤ (αVeq αV₂) (a₂ (αV cv)) (c₂ cv)) :
    Corres r ⊤ (αVeq αV₂) (a₁ >>= a₂) (c₁ >>= c₂) := by
  intro Q E
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  refine PartialOrder.rel_trans (r.γP_mono ((‹LawfulRefinement r CM AM›).wp_bind_le a₁ a₂ Q E)) ?_
  have hi : r.γP (wp a₁ (fun av => wp (a₂ av) Q E) E) ⊑
      wp c₁ (r.γQ (αVeq αV) (fun av => wp (a₂ av) Q E)) (r.γE E) :=
    PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl)
      (hc (fun av => wp (a₂ av) Q E) E)
  refine PartialOrder.rel_trans hi ?_
  refine PartialOrder.rel_trans
    (WP.wp_consequence c₁ _ (fun cv => wp (c₂ cv) (r.γQ (αVeq αV₂) Q) (r.γE E)) (r.γE E) ?_) ?_
  · intro cv
    simp only [Refinement.γQ_αVeq]
    have hfcv := hf cv Q E
    simp only [Refinement.γQ_αVeq] at hfcv
    exact PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl) hfcv
  · exact WPMonad.bind_le_wp_bind c₁ c₂ (r.γQ (αVeq αV₂) Q) (r.γE E)

/-- Branch congruence on a shared condition. -/
theorem corres_ite (r : Refinement CPred APred CEPred AEPred) {CVal AVal : Type w}
    (P : CPred) (αV : AVal → CVal → CPred) {cond : Prop} [Decidable cond]
    {a₁ a₂ : AM AVal} {c₁ c₂ : CM CVal}
    (h₁ : Corres r P αV a₁ c₁) (h₂ : Corres r P αV a₂ c₂) :
    Corres r P αV (if cond then a₁ else a₂) (if cond then c₁ else c₂) := by
  by_cases hc : cond <;> simp only [hc, if_true, if_false] <;> assumption

end Structural

/-! ## Composition of refinements -/

section Comp

variable {CPred BPred APred : Type w} {CEPred BEPred AEPred : Type w'}
  [Assertion CPred] [Assertion BPred] [Assertion APred]
  [Assertion CEPred] [Assertion BEPred] [Assertion AEPred]

/-- Compose refinements `C ← B` and `B ← A` into `C ← A`. -/
def Refinement.comp (r₁ : Refinement CPred BPred CEPred BEPred)
    (r₂ : Refinement BPred APred BEPred AEPred) : Refinement CPred APred CEPred AEPred where
  γP := r₁.γP ∘ r₂.γP
  γE := r₁.γE ∘ r₂.γE
  γP_mono h := r₁.γP_mono (r₂.γP_mono h)
  γE_mono h := r₁.γE_mono (r₂.γE_mono h)

/-- Correspondence composes (preconditions `⊤`): composing the refinements and value abstractions. -/
theorem corres_comp {CProg BProg AProg : Type _} {CVal BVal AVal : Type _}
    [WP CProg CVal CPred CEPred] [WP BProg BVal BPred BEPred] [WP AProg AVal APred AEPred]
    {r₁ : Refinement CPred BPred CEPred BEPred} {r₂ : Refinement BPred APred BEPred AEPred}
    {αV₁ : CVal → BVal} {αV₂ : BVal → AVal} {a : AProg} {b : BProg} {c : CProg}
    (hc : Corres r₁ ⊤ (αVeq αV₁) b c) (hb : Corres r₂ ⊤ (αVeq αV₂) a b) :
    Corres (r₁.comp r₂) ⊤ (αVeq (αV₂ ∘ αV₁)) a c := by
  intro Q E
  have hpost : (r₁.comp r₂).γQ (αVeq (αV₂ ∘ αV₁)) Q = r₁.γQ (αVeq αV₁) (r₂.γQ (αVeq αV₂) Q) := by
    simp only [Refinement.γQ_αVeq, Refinement.comp, Function.comp]
  rw [hpost]
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  have hb' : r₂.γP (wp a Q E) ⊑ wp b (r₂.γQ (αVeq αV₂) Q) (r₂.γE E) :=
    PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl) (hb Q E)
  have hc' := hc (r₂.γQ (αVeq αV₂) Q) (r₂.γE E)
  exact PartialOrder.rel_trans (r₁.γP_mono hb')
    (PartialOrder.rel_trans (le_meet _ _ _ (le_top _) PartialOrder.rel_refl) hc')

/-- Correspondence (precondition `⊤`) chains in `calc`/`Trans`. -/
instance {CProg BProg AProg : Type _} {CVal BVal AVal : Type _}
    [WP CProg CVal CPred CEPred] [WP BProg BVal BPred BEPred] [WP AProg AVal APred AEPred]
    {r₁ : Refinement CPred BPred CEPred BEPred} {r₂ : Refinement BPred APred BEPred AEPred}
    {αV₁ : CVal → BVal} {αV₂ : BVal → AVal} :
    Trans (Corres r₂ ⊤ (αVeq αV₂) : AProg → BProg → Prop)
      (Corres r₁ ⊤ (αVeq αV₁) : BProg → CProg → Prop)
      (Corres (r₁.comp r₂) ⊤ (αVeq (αV₂ ∘ αV₁)) : AProg → CProg → Prop) where
  trans hab hbc := corres_comp hbc hab

end Comp

/-! ## Identity refinement -/

section Id

variable {Pred : Type w} {EPred : Type w'} [Assertion Pred] [Assertion EPred]

/-- The refinement that is the identity on both assertion lattices. -/
def idRefinement (Pred : Type w) (EPred : Type w') [Assertion Pred] [Assertion EPred] :
    Refinement Pred Pred EPred EPred where
  γP := id
  γE := id
  γP_mono h := h
  γE_mono h := h

/-- Every program abstracts itself under the identity refinement, for any precondition. -/
theorem corres_id {Prog Val : Type _} [WP Prog Val Pred EPred] (P : Pred) (x : Prog) :
    Corres (idRefinement Pred EPred) P (αVeq (id : Val → Val)) x x := by
  intro Q E
  have hpost : (idRefinement Pred EPred).γQ (αVeq id) Q = Q := by
    funext cv; simp only [Refinement.γQ_αVeq, idRefinement, id_eq]
  rw [hpost]
  exact meet_le_right _ _

end Id

/-! ## Purification: dropping the state monad

An out-parameter is modelled as concrete *state*. When the concrete program is write-once (its
result and final state do not depend on the initial state), that state can be read off the exit and
returned as a pure *value*, eliminating the state monad. This is the terminal value coupling that
the state-aware `αV` was introduced for: `purifyαV av cv s := ⌜av = (cv, s)⌝` reads the entire
final state into the second component of the abstract result. It is sound only here, at the end of
the program, where there is no continuation whose control flow could depend on the read. -/

section Purify

/-- Drops an abstract `Id` assertion (a `Prop`) to a constant concrete-state predicate. The exit
read lives entirely in the value coupling `purifyαV`. -/
noncomputable def purifyRef (σ : Type) : Refinement (σ → Prop) Prop EPost.Nil EPost.Nil where
  γP φ := fun _ => φ
  γE := id
  γP_mono h := fun _ => h
  γE_mono h := h

/-- The terminal value coupling: `(cv, s)` abstracts a concrete return `cv` ending in state `s`. -/
def purifyαV {σ α : Type} : (α × σ) → α → (σ → Prop) :=
  fun av cv s => av = (cv, s)

/-- Under `purifyαV`, the postcondition concretization reads the final state into the result. -/
@[simp] theorem purifyRef_γQ {σ α : Type} (Q : (α × σ) → Prop) :
    (purifyRef σ).γQ purifyαV Q = fun cv s => Q (cv, s) := by
  funext cv s
  simp only [Refinement.γQ, purifyRef, purifyαV, iSup_apply, meet_apply, iSup_prop_eq_exists,
    meet_prop_eq_and]
  apply propext
  constructor
  · rintro ⟨i, rfl, h⟩; exact h
  · intro h; exact ⟨(cv, s), rfl, h⟩

/-- A write-once concrete program (its result `v` and final state `w` are independent of the initial
state) is abstracted by the pure return of its result-and-final-state, with no state monad. -/
theorem corres_purify {CProg σ α : Type} [WP CProg α (σ → Prop) EPost.Nil]
    (c : CProg) (v : α) (w : σ)
    (hc : ∀ (Q : α → σ → Prop) (E : EPost.Nil), (fun _ => Q v w) ⊑ wp c Q E) :
    Corres (purifyRef σ) ⊤ purifyαV (pure (v, w) : Id (α × σ)) c := by
  intro Q E
  rw [purifyRef_γQ]
  refine PartialOrder.rel_trans (PartialOrder.rel_trans (meet_le_right _ _) ?_)
    (hc (fun cv s => Q (cv, s)) E)
  apply le_of_forall_le
  intro s
  exact PartialOrder.rel_refl

end Purify

end Ascent
