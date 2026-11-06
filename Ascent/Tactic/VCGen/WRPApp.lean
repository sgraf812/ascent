import Lean.Meta.Sym.SymM
import Ascent.WRP
import Ascent.Table

/-!
# Goal metadata for `wrp` goals

`WRPApp` is the counterpart of `vcgen`'s `WPApp` for a goal `pre ⊑ wrp γ c a Q E s₁ … sₙ`. The
accessors carry the names of the `WPApp` accessors, so the translated modules use them unchanged:
`prog` is the concrete program `c`, `post` is the return relation `Q`, and `eposts` is the exception
relation `E`.
-/

open Lean Meta Sym

namespace Lean.Elab.Tactic.VCGen.Ascend

/-- The metadata of a goal whose right-hand side is `wrp γ c a Q E s₁ … sₙ`. -/
structure WRPApp where
  /-- The whole `wrp` application, including the excess state arguments. -/
  expr : Expr
  /-- The `wrp` function head. -/
  head : Expr
  /-- The 21 core arguments of `wrp`, ending with `γ, c, a, Q, E`. -/
  args : Array Expr
  /-- The arguments after `wrp … E`, the concrete state arguments. -/
  excessArgs : Array Expr

namespace WRPApp

/-- The position of the concrete program `c` among the core arguments. -/
def progIdx : Nat := 17

/-- The concrete program type `CProg`. -/
def Prog (info : WRPApp) : Expr := info.args[0]!
/-- The concrete monad, obtained by dropping the value type of `CProg`. -/
def M (info : WRPApp) : Expr :=
  if info.args[0]!.isApp then info.args[0]!.appFn! else info.args[0]!
/-- The concrete value type `CVal`. -/
def Value (info : WRPApp) : Expr := info.args[2]!
/-- The abstract value type `AVal`. -/
def AValue (info : WRPApp) : Expr := info.args[3]!
/-- The concrete assertion type `CPred`. -/
def Pred (info : WRPApp) : Expr := info.args[4]!
/-- The exception relation type `ERels`. -/
def EPosts (info : WRPApp) : Expr := info.args[8]!
/-- The `Assertion CPred` instance. -/
def instAL (info : WRPApp) : Expr := info.args[9]!
/-- The concrete `WP` instance. -/
def instWP (info : WRPApp) : Expr := info.args[13]!
/-- The concretization `γ`. -/
def γ (info : WRPApp) : Expr := info.args[16]!
/-- The concrete program `c`. -/
def prog (info : WRPApp) : Expr := info.args[17]!
/-- The abstract program `a`. -/
def abs (info : WRPApp) : Expr := info.args[18]!
/-- The return relation `Q`. -/
def post (info : WRPApp) : Expr := info.args[19]!
/-- The exception relation `E`. -/
def eposts (info : WRPApp) : Expr := info.args[20]!

/-- The arguments that the `Shim` lemmas take before the concrete program: the 17 arguments of
`wrp` before `c`, then `a`. -/
def lemmaPrefix (info : WRPApp) : Array Expr := (info.args.take 17).push info.args[18]!

/-- The `wrp` application itself, before the excess state arguments apply. -/
def wp (info : WRPApp) : Expr := info.expr.stripArgsN info.excessArgs.size

/-- The monad `m` of the program type `m α` on the concrete (`side = 0`) or abstract (`side = 1`)
side, with its `WPMonad m Pred EPosts` instance: read off a `WP` instance of the form
`instWPOfWPMonad m Pred EPosts α …`, else synthesized for the head of the program type. `none` for
a program type that is not monadic, such as kraken's `Program`. -/
def monadOf? (info : WRPApp) (side : Nat) : MetaM (Option (Expr × Expr)) := do
  let inst := info.args[13 + side]!
  if inst.isAppOfArity ``Std.WP.instWPOfWPMonad 8 then
    return some (inst.getAppArgs[0]!, inst.getAppArgs[7]!)
  let prog := info.args[side]!
  unless prog.isApp do return none
  let m := prog.appFn!
  let some ty ← observing? (mkAppOptM ``Std.WP.WPMonad
      #[m, info.args[4 + side]!, info.args[6 + side]!, none, info.args[9 + side]!, info.args[11 + side]!])
    | return none
  return (← synthInstance? ty).map (m, ·)

/-- The prefix with the abstract side replaced by fresh metavariables: the abstract value type, the
abstract `WP` instance in the spelling `instWPOfWPMonad m APred AEPosts ?α …`, and the abstract
program. The concrete side stays as the goal spells it. A rule built from it is specific to the
goal's concrete program type and to the abstract monad, and `abstractMVars` turns the
metavariables into rule parameters. An abstract program type that is not monadic is kept whole. -/
def schematic (info : WRPApp) : MetaM WRPApp := do
  let mut args := info.args
  if let some (m, inst) ← info.monadOf? 1 then
    let v ← mkFreshExprMVar (← Meta.inferType args[3]!)
    let instWP ← mkAppOptM ``Std.WP.instWPOfWPMonad
      #[m, args[5]!, args[7]!, v, none, args[10]!, args[12]!, inst]
    args := args.set! 3 v |>.set! 1 (mkApp m v) |>.set! 14 instWP
  args := args.set! 18 (← mkFreshExprMVar (userName := `a) args[1]!)
  return { info with args, expr := mkAppN info.head (args ++ info.excessArgs) }

/-- The arguments a rule built from `schematic` bakes in, as one term for hash-consing: the
concrete `WP` instance, as core's key; the abstract monad where `monadOf?` finds one, else the
abstract program type and its `WP` instance; the abstract assertion type, the abstract exception
postcondition type, the exception relation type, and `γ`. `γ` is baked in so that a structured
concretization is unified once, at rule construction, and then compared by pointer at every
application. The term is a key, never a well-typed expression. -/
def ruleKey (info : WRPApp) : MetaM Expr := do
  let abs ← match ← info.monadOf? 1 with
    | some (m, _) => pure #[m]
    | none => pure #[info.args[1]!, info.args[14]!]
  return mkAppN (mkConst `Ascent.ruleKey)
    (#[info.instWP] ++ abs ++ #[info.args[5]!, info.args[7]!, info.args[8]!, info.γ])

end WRPApp

/-- The `wrp` metadata of `rhs`, or `none` when `rhs` is not a `wrp` application. -/
def isWRPApp? (rhs : Expr) : Option WRPApp :=
  rhs.withApp fun head args =>
    if head.isConstOf ``Ascent.wrp && args.size ≥ 21 then
      some { expr := rhs, head, args := args.take 21, excessArgs := args.drop 21 }
    else
      none

end Lean.Elab.Tactic.VCGen.Ascend
