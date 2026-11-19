import DistilleryTests.Regress.StateSplit

/-!
# A match on a word becomes a chain of `if`s on its number

The state is a word `s : BitVec 8`. The abstract program reads the number `n` of the word, with the
entry `PureRefinement s n True WordNat`. The concrete program matches `s` against the literals `0`
and `1`, with a final wildcard. The run rewrites the `match` into the chain
`if h : s = 0#8 then … else if h : s = 1#8 then … else …`, and the value solver abstracts each
condition `s = k#8` to `n = k` under the guards `n < 2 ^ 8` and `k < 2 ^ 8`. The abstract program
is the same chain on `n`. The test pins the deviation "two-sided split" of `docs/vcgen-fork.md`.
-/

open Std.WP Lean.Order Distillery StateSplitTest

namespace WordMatchTest

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

attribute [local distill] wrp_bind

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
info: def WordMatchTest.progWordA : SM (BitVec 8) Unit :=
do
  let x ← getNat
  if h : x = 0 then set 5 else if h : x = 1 then set 7 else set 9
-/
#guard_msgs in
#print progWordA

end WordMatchTest
