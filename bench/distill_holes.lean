import Driver
import Cases.Holes

/-! # `Holes`, engine measurements -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.Holes

def mk (n : Nat) : MetaM Problem := do
  let xs := (List.range n).toArray.map fun i => mkIdent (Name.mkSimple s!"x{i}")
  let sum ← (xs.extract 1 n).foldlM (init := (xs[0]! : Term)) fun acc x => `($acc + $x)
  let prog ← (List.range n).foldrM (init := ← `((pure $sum : Demonic Nat))) fun i k =>
    `((pure (y + $(quote (i + 1))) : Demonic Nat) >>= fun $(xs[i]!) => $k)
  return {
    binders := #[← `(bracketedBinder| (y : Nat))]
    stmt := ← `(⦃(⊤ : Prop)⦄ ($prog) ⪯[γp] (?_ : Demonic Nat) ⦃(⌜· = ·⌝)⦄) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "Holes" mk [] `(tactic| distill) `(tactic| grind) [25, 50, 75]
