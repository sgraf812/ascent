import Lean.Meta.Sym.SymM
import Ascent.WRP

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

/-- The arguments of the prefix that a spec rule bakes in, as one term for hash-consing: the
concrete `WP` instance, the abstract monad, the abstract lattice types, the exception relation
type and `γ`. The term is a key, never a well-typed expression. -/
def ruleKey (info : WRPApp) : Expr :=
  let AM := if info.args[1]!.isApp then info.args[1]!.appFn! else info.args[1]!
  mkAppN (mkConst `Ascent.ruleKey)
    #[info.instWP, AM, info.args[5]!, info.args[7]!, info.args[8]!, info.γ]

end WRPApp

/-- The `wrp` metadata of `rhs`, or `none` when `rhs` is not a `wrp` application. -/
def isWRPApp? (rhs : Expr) : Option WRPApp :=
  rhs.withApp fun head args =>
    if head.isConstOf ``Ascent.wrp && args.size ≥ 21 then
      some { expr := rhs, head, args := args.take 21, excessArgs := args.drop 21 }
    else
      none

end Lean.Elab.Tactic.VCGen.Ascend
