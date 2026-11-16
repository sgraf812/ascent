import Ascent.Demonic

/-!
# The public interface of `Demonic`

The `wp` of each operation, the absorption of undefined behaviour by `bind`, the miracle `magic`,
and program equality through `wp` (`Demonic.ext`). Only the public interface is used.
-/

open Std.WP

namespace Ascent.DemonicTests

example (Q : Nat → Prop) : wp (Demonic.abort : Demonic Nat) Q estack⟨⟩ = False := rfl

example (p Q : Nat → Prop) : wp (Demonic.select p) Q estack⟨⟩ = ∀ a, p a → Q a := rfl

example (Q : Nat → Prop) : wp (Demonic.unknown : Demonic Nat) Q estack⟨⟩ = ∀ a, Q a :=
  Demonic.wp_unknown_eq Q _

example (Q : Nat → Prop) : wp (Demonic.magic : Demonic Nat) Q estack⟨⟩ = True :=
  Demonic.wp_magic_eq Q _

example (g : Prop) (Q : Unit → Prop) : wp (Demonic.assert g) Q estack⟨⟩ = (g ∧ Q ()) := rfl

example (g : Prop) (Q : Unit → Prop) : wp (Demonic.assume g) Q estack⟨⟩ = (g → Q ()) :=
  Demonic.wp_assume_eq g Q _

-- A failed `assert` is undefined behaviour, a failed `assume` has no outcome.
example : Demonic.assert False = Demonic.abort := Demonic.assert_of_neg id
example : Demonic.assume False = Demonic.magic := Demonic.assume_of_neg id

-- One aborting branch makes the whole program abort.
example : (Demonic.unknown >>= fun b : Bool => if b then Demonic.abort else pure 1) = Demonic.abort :=
  Demonic.ext (funext fun _ => propext ⟨fun h => by simpa using h true trivial, False.elim⟩)

-- A singleton `select` is `pure`.
example (a : Nat) : Demonic.select (· = a) = pure a :=
  Demonic.ext (funext fun _ => propext ⟨fun h => h a rfl, fun h _ hb => hb ▸ h⟩)

-- `select` composes: two choices are one choice over the reachable values.
example : (Demonic.select (· < 2) >>= fun n => Demonic.select (· = n + 1))
    = Demonic.select (fun m => 0 < m ∧ m < 3) := by
  refine Demonic.ext (funext fun Q => propext ⟨fun h m ⟨h0, h3⟩ => ?_, fun h n hn m hm => ?_⟩)
  · exact h (m - 1) (by omega) m (by omega)
  · exact h m (by omega)

end Ascent.DemonicTests
