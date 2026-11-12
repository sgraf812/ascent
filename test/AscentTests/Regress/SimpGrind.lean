import Ascent.Tactic.VCGen.Command

/-!
# A side condition of `sym_simp_def` closed by `grind`

The rule `twice_sub` holds under the condition `a ≤ 2 * a`, which `Sym.simp` does not prove and
`grind` does. `sym_simp_def` rewrites with the rule.
-/

namespace SimpGrindTest

theorem twice_sub (a : Nat) (_h : a ≤ 2 * a) : 2 * a - a = a := by omega

sym_simp_def f (a : Nat) : Nat from 2 * a - a using pre [] post [twice_sub]

/--
info: def SimpGrindTest.f : Nat → Nat :=
fun a => a
-/
#guard_msgs in
#print f

end SimpGrindTest
