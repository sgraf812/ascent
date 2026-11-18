import Cases.Setup.State

/-!
# `DiteSplit`: a dependent `if` on a value read from the state

The mirror of the `vcgen` case `DiteSplit`, in `EM Nat`. Each step reads the state into `s`, throws
when `s > v`, and otherwise adds and subtracts `v`. The condition mentions the read value, so the
run abstracts it to the abstract read value before the split. The `then` branch is `throw … >>= k`
with an unreachable continuation `k`, which `wrp_throw_bind_EM` drops. The family stresses the
abstraction of a split condition and the two-sided split of a `dite`.
-/

open Std.WP Lean.Order Distillery DistillBench.State

namespace DistillBench.DiteSplit

attribute [distill] wrp_bind wrp_get_EM wrp_set_EM wrp_throw_EM wrp_pure_unit_EM
attribute [distill high] wrp_throw_bind_EM
attribute [distill_pure low] abs_refl
attribute [distill_pure] abs_add abs_sub abs_gt

def step (v : Nat) : EM Nat Unit := do
  let s ← get
  if _ : s > v then
    throw "s is too large"
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : EM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

end DistillBench.DiteSplit
