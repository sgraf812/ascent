import Ascent.UB.StateT
import Ascent.Table
import Ascent.PureRefinement
import Ascent.Tactic.VCGen.Command

/-!
# A toy block machine

The regression tests run `ascend` on this machine instead of an instruction set. A block program is
a computation in `BlockM σ`: an exception is a jump to a label. The concrete state `CS` has one
register `r` and a zero flag `zf`. The abstract state is the register alone, so a flag that a later
step reads must become a value of the abstract program.

The steps are `modifyIf g f` (undefined behaviour unless `g`, then `f`), `branch c l` (jump to `l`
if `c`), and `peek c` (read `c` from the state). The concrete instructions are `decC` (decrement
`r`, set `zf`), `jnzC l` (jump if `zf` is clear) and `setC v`. `cells` runs the cells of a table in
order; its rule `wrp_cells` asks for one refinement per cell, which `ascend` collects into an
abstract table.
-/

open Std.WP Lean.Order Ascent
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Blocks

inductive Lbl where
  | lbl (n : Nat)
  | exit
  deriving DecidableEq, Inhabited

abbrev BlockM (σ : Type) := ExceptT Lbl (StateT σ UB)

section
variable {σ : Type}

noncomputable def modifyIf (g : σ → Prop) (f : σ → σ) : BlockM σ Unit :=
  fun st => UB.assume (g st) >>= fun _ => pure (.ok (), f st)

def branch (c : σ → Bool) (l : Lbl) : BlockM σ Unit :=
  fun st => if c st then pure (.error l, st) else pure (.ok (), st)

def peek {β : Type} (c : σ → β) : BlockM σ β :=
  fun st => pure (.ok (c st), st)

variable (Qa : Unit → σ → Prop) (Ea : (Lbl → σ → Prop) × EStack⟨⟩) (st : σ)

theorem wp_modifyIf (g f) : wp (modifyIf g f) Qa Ea st = (g st ∧ Qa () (f st)) := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, show (modifyIf g f).run.run st = modifyIf g f st from rfl]
  unfold modifyIf
  by_cases h : g st
  · rw [UB.assume_bind_of_pos h]
    simp only [UB.wp_pure_eq, h, true_and]
    rfl
  · rw [UB.assume_bind_of_neg h]
    simp only [UB.wp_fail_eq, bot_prop_eq, h, false_and]

theorem wp_branch (c l) : wp (branch c l) Qa Ea st = if c st then Ea.1 l st else Qa () st := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, show (branch c l).run.run st = branch c l st from rfl]
  unfold branch
  split
  · simp only [UB.wp_pure_eq, *]
    rfl
  · simp only [UB.wp_pure_eq, *]
    rfl

theorem wp_peek {β : Type} {Qb : β → σ → Prop} (c : σ → β) : wp (peek c) Qb Ea st = Qb (c st) st := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq, show (peek c).run.run st = peek c st from rfl]
  simp only [peek, UB.wp_pure_eq]
  rfl

end

structure CS where
  r : BitVec 64
  zf : Bool

def view (s : CS) : BitVec 64 := s.r

@[vcgen_simp] theorem view_mk (r : BitVec 64) (zf : Bool) : view ⟨r, zf⟩ = r := rfl

noncomputable def decC : BlockM CS Unit := modifyIf (fun _ => True) fun s => ⟨s.r - 1, s.r - 1 == 0⟩
def jnzC (l : Nat) : BlockM CS Unit := branch (fun s => !s.zf) (.lbl l)
noncomputable def setC (v : BitVec 64) : BlockM CS Unit := modifyIf (fun _ => True) fun s => ⟨v, s.zf⟩

section
variable {Q : Unit → Unit → CS → Prop} {E : (Lbl → Lbl → CS → Prop) × EStack⟨⟩}

@[ascend] theorem wrp_decC {Qb : Unit → Bool → CS → Prop} :
    (fun s => ∀ z, PureRefinement (s.r - 1 == 0) z True Eq → Qb () z ⟨s.r - 1, s.r - 1 == 0⟩)
      ⊑ wrp (ofStateRepr view) decC
          (do
            let z ← peek fun (a : BitVec 64) => a - 1 == 0
            modifyIf (fun _ => True) (· - 1)
            pure z : BlockM (BitVec 64) Bool) Qb E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq, wp_peek,
    wp_modifyIf, WPMonadExact.wp_pure_eq] at hs
  obtain ⟨hk, -, hw⟩ := hs
  simp only [decC, wp_modifyIf, true_and]
  rw [Concretization.post_pi]
  exact ⟨_, hk _ (PureRefinement.of_rel rfl), hw⟩

@[ascend] theorem wrp_jnzC (l : Nat) (b : Bool) :
    (fun s => PureRefinement (!s.zf) b True Eq ∧ (b = true → E.1 (.lbl l) (.lbl l) s) ∧
      (b = false → Q () () s))
      ⊑ wrp (ofStateRepr view) (jnzC l) (branch (fun _ => b) (.lbl l)) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_branch] at hs
  obtain ⟨⟨hb, hjmp, hfall⟩, hw⟩ := hs
  have hc : (!s.zf) = b := hb trivial
  simp only [jnzC, wp_branch, hc]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hw ⊢
    rw [Concretization.post_pi]
    exact ⟨(), hfall rfl, hw⟩
  · simp only [↓reduceIte] at hw ⊢
    show (ofStateRepr view).post E.1 Ea.1 (.lbl l) s
    rw [Concretization.post_pi]
    exact ⟨.lbl l, hjmp rfl, hw⟩

@[ascend] theorem wrp_setC (v : BitVec 64) :
    (fun s => Q () () ⟨v, s.zf⟩)
      ⊑ wrp (ofStateRepr view) (setC v) (modifyIf (fun _ => True) fun _ => v : BlockM (BitVec 64) Unit)
          Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_modifyIf, true_and] at hs
  simp only [setC, wp_modifyIf, true_and]
  rw [Concretization.post_pi]
  exact ⟨(), hs.1, hs.2⟩

end

@[ascend_pure low] theorem abs_refl {α : Type} {c : α} : PureRefinement c c True Eq := fun _ => rfl

@[ascend_pure] theorem abs_not {c x : Bool} {P : Prop} (h : PureRefinement c x P Eq) :
    PureRefinement (!c) (!x) P Eq :=
  fun hp => by rw [h hp]

/-! ## Tables of cells -/

def cells {σ : Type} (tbl : Table Nat (BlockM σ Unit)) : BlockM σ Unit := tbl.forM fun kc => kc.2

def cellsAt {σ : Type} (tbl : Table Nat (BlockM σ Unit)) (ks : List Nat) : BlockM σ Unit :=
  ks.forM (Table.get tbl)

@[ascend] theorem wrp_cells {I : CS → Prop} {E : (Lbl → Lbl → CS → Prop) × EStack⟨⟩}
    (ctbl : Table Nat (BlockM CS Unit)) {atbl : Table Nat (BlockM (BitVec 64) Unit)}
    (h : ∀ kc ∈ ctbl, ⦃I⦄ kc.2 ⪯[ofStateRepr view] (Table.get atbl kc.1) ⦃fun _ _ => I; E⦄) :
    I ⊑ wrp (ofStateRepr view) (cells ctbl) (cellsAt atbl (ctbl.map Prod.fst)) (fun _ _ => I) E := by
  induction ctbl with
  | nil => exact wrp_pure (Q := fun _ _ => I) () ()
  | cons kc rest ih =>
    simp only [cells, cellsAt, List.map_cons] at ih ⊢
    refine PartialOrder.rel_trans ?_ wrp_bind
    exact PartialOrder.rel_trans (h kc List.mem_cons_self).le_wrp
      (wrp_mono_post fun _ _ => ih fun x hx => h x (List.mem_cons_of_mem _ hx))

end Ascent.Blocks
