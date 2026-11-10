import Ascent.BlockLoop

/-!
# Catching an exit

A block program `b` leaves a function through the exception `e`. `catchExit e b` is the function:
it returns where `b` throws `e`, and throws every other label again. The layers of a refinement
chain relate such caught programs, and their structuring passes remove the catch by equations.

`Refinement.transport_catchExit` connects the chain to the concrete program at the top: a triple
about `catchExit e b` and a refinement of the concrete program to `b` give a triple about the
concrete program, whose exception postcondition at `e` is the return postcondition of the caught
program.
-/

open Std.WP Lean.Order

namespace Ascent

section
variable {κ σ : Type} [DecidableEq κ]

def catchExit (e : κ) (b : ExceptT κ (StateT σ UB) Unit) : ExceptT κ (StateT σ UB) Unit :=
  tryCatch b (fun l => if l = e then pure () else throw l)

theorem wp_catchExit (e : κ) (b : ExceptT κ (StateT σ UB) Unit) (Q : Unit → σ → Prop)
    (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (catchExit e b) Q E s = wp b Q (fun l t => if l = e then Q () t else E.1 l t, E.2) s := by
  have h : (fun l => wp (if l = e then pure () else throw l : ExceptT κ (StateT σ UB) Unit) Q E)
      = fun l t => if l = e then Q () t else E.1 l t := by
    funext l t
    by_cases hl : l = e
    · simp [hl, WPMonadExact.wp_pure_eq]
    · simp [hl, BlockLoop.wp_throw]
  rw [catchExit, BlockLoop.wp_tryCatch, h]

end

section
variable {κ σ : Type} [DecidableEq κ] {CProg CVal CPred CEPosts : Type _} {ERels : Type _}
  [Assertion CPred] [Assertion CEPosts] [WP CProg CVal CPred CEPosts]
  [EPostsConcretization CPred (σ → Prop) CEPosts ((κ → σ → Prop) × EStack⟨⟩) ERels]
  [Heyting CPred]

theorem Refinement.transport_catchExit {e : κ} {γ : Concretization CPred (σ → Prop)}
    {P : CPred} {Q : CVal → Unit → CPred} {E : ERels} {c : CProg} {b : ExceptT κ (StateT σ UB) Unit}
    {Pb : σ → Prop} {Qb : Unit → σ → Prop} {Eb : (κ → σ → Prop) × EStack⟨⟩}
    (h : ⦃P⦄ c ⪯[γ] b ⦃Q; E⦄) (hb : Triple (catchExit e b) Pb Qb Eb) :
    Triple c (P ⊓ γ.pred Pb) (γ.post Q Qb)
      (EPostsConcretization.ePosts γ E
        ((fun l t => if l = e then Qb () t else Eb.1 l t, Eb.2) : (κ → σ → Prop) × EStack⟨⟩)) :=
  h.transport ⟨fun s hs => (wp_catchExit e b Qb Eb s).mp (hb.le_wp s hs)⟩

end

end Ascent
