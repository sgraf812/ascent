import Distillery.Demonic.StateT
import Distillery.PureRefinement
import Distillery.Tactic.VCGen.Command
import DistilleryTests.Setup.Blocks

/-!
# Splits of `if` and `match`

Each section runs `distill` on a concrete program that branches with an `if`, a dependent `if` or
a `match`, and pins the abstract program that the run synthesizes. The file pins the deviation
"two-sided split" of `docs/vcgen-fork.md`.
-/

open Std.WP Lean.Order Distillery

namespace SplitTest

/-!
## An `if` on a variable

Regression for `a14ae3e`: the split of an `if` on a `wrp` goal splits the concrete and the abstract
program on the same condition, with one fresh abstract branch per alternative.
-/

section
open Distillery.Blocks
open Distillery.Concretization (ofStateRepr)

attribute [local distill] wrp_bind wrp_pure

distill_def sp (b : Bool) : BlockM (BitVec 64) Unit from
  ⦃fun _ => True⦄ (if b = true then setC 1 else setC 2) ⪯[ofStateRepr view] sp
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill []

example (b : Bool) :
    sp b = if b = true then modifyIf (fun _ => True) fun _ => 1 else modifyIf (fun _ => True) fun _ => 2 :=
  rfl

end

/-!
## A split on a value that the run reads from the state

The program reads the state into `s` and splits on `s` with an `if`, a dependent `if` and a
`match`. The run binds `s` to the abstract variable `x` of the abstract program, with the entry
`PureRefinement s x True Eq`. The value solver abstracts the condition `1 < s` to `1 < x` and the
discriminant `s` to `x`, so the abstract program splits on `x`, and the abstract `match` has one
alternative for each concrete alternative.
-/

abbrev SM (σ : Type) := StateT σ Demonic

abbrev γ (σ : Type) : Concretization (σ → Prop) (σ → Prop) := Concretization.id (σ → Prop)

section
variable {σ : Type}

theorem wp_get_SM (Q : σ → σ → Prop) (E : EStack⟨⟩) (s : σ) : wp (get : SM σ σ) Q E s = Q s s := rfl

theorem wp_set_SM (v : σ) (Q : PUnit → σ → Prop) (E : EStack⟨⟩) (s : σ) :
    wp (set v : SM σ PUnit) Q E s = Q ⟨⟩ v := rfl

@[distill] theorem wrp_get_SM {Q : σ → σ → σ → Prop} {E : EStack⟨⟩} :
    (fun s => ∀ x, PureRefinement s x True Eq → Q s x s)
      ⊑ wrp (γ σ) (get : SM σ σ) (get : SM σ σ) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_get_SM] at h ⊢
  rw [Concretization.post_pi]
  exact ⟨s, h.1 s (PureRefinement.of_rel rfl), h.2⟩

@[distill] theorem wrp_set_SM (v w : σ) {Q : PUnit → PUnit → σ → Prop} {E : EStack⟨⟩} :
    (fun _ => PureRefinement v w True Eq ∧ Q ⟨⟩ ⟨⟩ v)
      ⊑ wrp (γ σ) (set v : SM σ PUnit) (set w : SM σ PUnit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_set_SM] at h ⊢
  obtain ⟨⟨hv, hq⟩, ha⟩ := h
  cases (hv trivial : v = w)
  rw [Concretization.post_pi]
  exact ⟨⟨⟩, hq, ha⟩

end

@[distill_pure low] theorem abs_eq_refl {α : Type} {c : α} : PureRefinement c c True Eq := fun _ => rfl

@[distill_pure] theorem abs_lt {a b x y : Nat} {P₁ P₂ : Prop} (h₁ : PureRefinement a x P₁ Eq)
    (h₂ : PureRefinement b y P₂ Eq) : PureRefinement (a < b) (x < y) (P₁ ∧ P₂) Eq :=
  fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

@[distill_pure] theorem abs_sub {a b x y : Nat} {P₁ P₂ : Prop} (h₁ : PureRefinement a x P₁ Eq)
    (h₂ : PureRefinement b y P₂ Eq) : PureRefinement (a - b) (x - y) (P₁ ∧ P₂) Eq :=
  fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

attribute [local distill] wrp_bind

def progIte : SM Nat Unit := do let s ← get; if 1 < s then set 0 else set s

distill_def progIteA : SM Nat Unit from
  ⦃fun _ => True⦄ progIte ⪯[γ Nat] progIteA ⦃fun _ _ _ => True⦄
  distill [progIte]

/--
info: def SplitTest.progIteA : SM Nat Unit :=
do
  let x ← get
  if 1 < x then set 0 else set x
-/
#guard_msgs in
#print progIteA

def progDite : SM Nat Unit := do let s ← get; if _ : 1 < s then set (s - 1) else set s

distill_def progDiteA : SM Nat Unit from
  ⦃fun _ => True⦄ progDite ⪯[γ Nat] progDiteA ⦃fun _ _ _ => True⦄
  distill [progDite]

/--
info: def SplitTest.progDiteA : SM Nat Unit :=
do
  let x ← get
  if h : 1 < x then set (x - 1) else set x
-/
#guard_msgs in
#print progDiteA

def progMatch : SM Nat Unit := do
  let s ← get
  match s with
  | 0 => set 1
  | n + 1 => set n

distill_def progMatchA : SM Nat Unit from
  ⦃fun _ => True⦄ progMatch ⪯[γ Nat] progMatchA ⦃fun _ _ _ => True⦄
  distill [progMatch]

/--
info: def SplitTest.progMatchA : SM Nat Unit :=
do
  let x ← get
  match x with
    | 0 => set 1
    | n.succ => set n
-/
#guard_msgs in
#print progMatchA

/-!
## A match on literals becomes a chain of `if`s

The program `progLit` reads the state into `s` and matches `s` against the literals `0` and `1`,
with a final variable pattern `m`. The run rewrites the `match` into the chain
`if h : s = 0 then … else if h : s = 1 then … else …`, and the value solver abstracts each
condition `s = k` to `x = k`. The abstract program is the same chain on `x`, and its last branch
refines the alternative of `m` at `x`. The program `progBool` matches `s == 3` against `true` and
`false`, without a variable pattern: the alternative of `false` is the last `else`.
-/

@[distill_pure] theorem abs_eq {α : Type} {a b x y : α} {P₁ P₂ : Prop} (h₁ : PureRefinement a x P₁ Eq)
    (h₂ : PureRefinement b y P₂ Eq) : PureRefinement (a = b) (x = y) (P₁ ∧ P₂) Eq :=
  fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

def progLit : SM Nat Unit := do
  let s ← get
  match s with
  | 0 => set 5
  | 1 => set 7
  | m => set (m - 1)

distill_def progLitA : SM Nat Unit from
  ⦃fun _ => True⦄ progLit ⪯[γ Nat] progLitA ⦃fun _ _ _ => True⦄
  distill [progLit]

/--
info: def SplitTest.progLitA : SM Nat Unit :=
do
  let x ← get
  if h : x = 0 then set 5 else if h : x = 1 then set 7 else set (x - 1)
-/
#guard_msgs in
#print progLitA

@[distill_pure] theorem abs_beq {a b x y : Nat} {P₁ P₂ : Prop} (h₁ : PureRefinement a x P₁ Eq)
    (h₂ : PureRefinement b y P₂ Eq) : PureRefinement (a == b) (x == y) (P₁ ∧ P₂) Eq :=
  fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

def progBool : SM Nat Unit := do
  let s ← get
  match s == 3 with
  | true => set 5
  | false => set s

distill_def progBoolA : SM Nat Unit from
  ⦃fun _ => True⦄ progBool ⪯[γ Nat] progBoolA ⦃fun _ _ _ => True⦄
  distill [progBool]

/--
info: def SplitTest.progBoolA : SM Nat Unit :=
do
  let x ← get
  if h : (x == 3) = true then set 5 else set x
-/
#guard_msgs in
#print progBoolA

/-!
## A match on a word becomes a chain of `if`s on its number

The state is a word `s : BitVec 8`. The abstract program reads the number `n` of the word, with the
entry `PureRefinement s n True WordNat`. The concrete program matches `s` against the literals `0`
and `1`, with a final wildcard. The run rewrites the `match` into the chain
`if h : s = 0#8 then … else if h : s = 1#8 then … else …`, and the value solver abstracts each
condition `s = k#8` to `n = k` under the guards `n < 2 ^ 8` and `k < 2 ^ 8`. The abstract program
is the same chain on `n`.
-/

def WordNat (x : BitVec 8) (n : Nat) : Prop := x = BitVec.ofNat 8 n

def getNat : SM (BitVec 8) Nat := do let s ← get; pure s.toNat

@[distill high] theorem wrp_get_nat {Q : BitVec 8 → Nat → BitVec 8 → Prop} {E : EStack⟨⟩} :
    (fun s => ∀ n, PureRefinement s n True WordNat → n < 2 ^ 8 → Q s n s)
      ⊑ wrp (γ (BitVec 8)) (get : SM (BitVec 8) (BitVec 8)) getNat Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_get_SM] at h ⊢
  rw [Concretization.post_pi]
  exact ⟨s.toNat, h.1 s.toNat (PureRefinement.of_rel (BitVec.ofNat_toNat 8 s).symm)
    s.isLt, h.2⟩

@[distill_pure] theorem absN_eq_lit {x : BitVec 8} {n k : Nat} {P : Prop}
    (h : PureRefinement x n P WordNat) :
    PureRefinement (x = BitVec.ofNat 8 k) (n = k) (P ∧ n < 2 ^ 8 ∧ k < 2 ^ 8) Eq :=
  fun ⟨hp, hn, hk⟩ => by
    rw [h hp]
    refine propext ⟨fun e => ?_, fun e => e ▸ rfl⟩
    have := congrArg BitVec.toNat e
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hk] using this

def progWord : SM (BitVec 8) Unit := do
  let s ← get
  match s with
  | 0 => set (5 : BitVec 8)
  | 1 => set (7 : BitVec 8)
  | _ => set (9 : BitVec 8)

distill_def progWordA : SM (BitVec 8) Unit from
  ⦃fun _ => True⦄ progWord ⪯[γ (BitVec 8)] progWordA ⦃fun _ _ _ => True⦄
  distill [progWord] with finish

/--
info: def SplitTest.progWordA : SM (BitVec 8) Unit :=
do
  let x ← getNat
  if h : x = 0 then set 5 else if h : x = 1 then set 7 else set 9
-/
#guard_msgs in
#print progWordA

end SplitTest
