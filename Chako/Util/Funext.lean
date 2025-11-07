module
public import Lean.Meta.Basic
import Lean.Meta.Transform
import Lean.Meta.AppBuilder

/-!
This module contains infrastructure to apply function extensionality. This is required because we
might end up in situations where we have two functions such as `f g : (n : Nat) → Fin n → Bool` and
might want to prove them equal `f = g`. However, they are going to be eliminated to
`f g : Nat → Nat → Bool` at which point the constraint that the second argument is bounded above by
the first is gone. We can counteract this by applying extensionality explicitly:
`∀ (n : Nat) (x : Fin n), f n x = g n x`. In this formula we explicitly quantify over `(x : Fin n)`
which will provoke the encoder to place an invariant on `x`.

Note that we do not generally apply extensionality everywhere: If we are within a function body
contains a predicate of the shape `f = g` where `f` is a polymorphic function we would introduce a
binder `∀ (α : Type u)` which our encoder cannot handle in this position.
-/

namespace Chako
namespace Util

open Lean

def funext (args : Array Expr) : MetaM Expr := do
  let α := args[0]!
  Meta.forallTelescope α fun arr _ => do
    Meta.withLocalDeclsDND #[(`l, α), (`r, α)] fun lr => do
      let lhs := mkAppN lr[0]! arr
      let rhs := mkAppN lr[1]! arr
      trace[chako] m!"Funext lhs: {lhs}, rhs: {rhs}"
      let inner ← Meta.mkForallFVars arr (← Meta.mkEq lhs rhs)
      trace[chako] m!"Funext inner: {inner}"
      let wrapper ← Meta.mkLambdaFVars lr inner
      trace[chako] m!"Funext outer: {wrapper}"
      return mkAppN wrapper args[1:] |>.headBeta

public def funextTransform (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := pre)
where
  pre (e : Expr) : MetaM TransformStep := do
    e.withApp fun fn args => do
      let .const ``Eq [_] := fn | return .continue
      if args.isEmpty then return .continue
      let α := args[0]!
      if !α.isForall then return .continue
      let newTarget ← funext args
      return .visit newTarget

end Util
end Chako
