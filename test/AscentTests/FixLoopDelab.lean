import Ascent.FixLoop.Delab

open Ascent

namespace AscentTests.FixLoopDelab

noncomputable def fill (n : Nat) : StateM (Array Nat) Unit :=
  FixLoop.mk.forIn 0 (fun _ i => do
    modify (·.push i)
    if ¬n = i + 1 then pure (.yield (i + 1)) else pure (.done i)) >>= fun _ => pure ()

/--
info: def AscentTests.FixLoopDelab.fill : Nat → StateM (Array Nat) Unit :=
fun n => do
  let mut i := 0
  repeat'
    modify fun x => x.push i
    if ¬n = i + 1 then 
      i := i + 1
    else
      break
-/
#guard_msgs in
#print fill

noncomputable def fill' (n : Nat) : StateM (Array Nat) Unit := do
  let mut i := 0
  repeat'
    modify fun x => x.push i
    if ¬n = i + 1 then
      i := i + 1
    else
      break

example : fill = fill' := rfl

noncomputable def count (n : Nat) : StateM Nat Nat :=
  FixLoop.mk.forIn 0 fun _ i =>
    if i < n then do modify (· + 1); pure (.yield (i + 1)) else pure (.done i)

/--
info: def AscentTests.FixLoopDelab.count : Nat → StateM Nat Nat :=
fun n => do
  let mut i := 0
  while' i < n do
    modify fun x => x + 1
    i := i + 1
  pure i
-/
#guard_msgs in
#print count

noncomputable def count' (n : Nat) : StateM Nat Nat := do
  let mut i := 0
  while' i < n do
    modify fun x => x + 1
    i := i + 1
  pure i

example : count = count' := rfl

end AscentTests.FixLoopDelab
