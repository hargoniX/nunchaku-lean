module
public import Lean.Meta.Basic
import Lean.Meta.Transform
import Lean.Meta.AppBuilder

namespace Chako
namespace Util

open Lean

public def funext (args : Array Expr) (allowTypeQuant : Bool) : MetaM Expr := do
  let α := args[0]!
  Meta.forallTelescope α fun arr _ => do
    if !allowTypeQuant then
      arr.forM fun part => do
        let ty ← Meta.inferType part
        if let .sort u := ty then
          if !u.isAlwaysZero then
            throwError m!"Type quantification in function extensionality transformation: {α} {args}"
    Meta.withLocalDeclsDND #[(`l, α), (`r, α)] fun lr => do
      let lhs := mkAppN lr[0]! arr
      let rhs := mkAppN lr[1]! arr
      trace[chako] m!"Funext lhs: {lhs}, rhs: {rhs}"
      let inner ← Meta.mkForallFVars arr (← Meta.mkEq lhs rhs)
      trace[chako] m!"Funext inner: {inner}"
      let wrapper ← Meta.mkLambdaFVars lr inner
      trace[chako] m!"Funext outer: {wrapper}"
      return mkAppN wrapper args[1:] |>.headBeta

public def funextTransform (e : Expr) (allowTypeQuant : Bool) : MetaM Expr := do
  Meta.transform e (pre := pre)
where
  pre (e : Expr) : MetaM TransformStep := do
    e.withApp fun fn args => do
      let .const ``Eq [_] := fn | return .continue
      if args.isEmpty then return .continue
      let α := args[0]!
      if !α.isForall then return .continue
      let newTarget ← funext args allowTypeQuant
      return .visit newTarget

end Util
end Chako
