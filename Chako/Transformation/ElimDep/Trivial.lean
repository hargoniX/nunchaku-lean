module
import Chako.Transformation.ElimDep.Basic
public import Lean.Meta.Basic

/-!
This module contains the logic for determining whether the invariant associated with a type is
always going to be trivially true, this allows us to drop them almost all of the time.
-/

namespace Chako
namespace Transformation
namespace ElimDep

open Lean

structure TrivialState where
  visited : Std.HashSet Name := {}

structure TrivialCtx where
  knownTrivial : PersistentHashSet Expr := {}

abbrev TrivialM := ReaderT TrivialCtx StateRefT TrivialState MetaM

mutual

/--
Invariant: Only invoked when we know that:
1. The inductive is index free
2. The inductive only has type level params
-/
private partial def visitCtor (info : ConstructorVal) : TrivialM Bool := do
  let simplifiedType ← unfoldTypeAliases info.type
  let hasSimpleType ← Meta.forallTelescope simplifiedType fun args _ => do
    let params := args[0...info.numParams].toArray
    let remainder := args[info.numParams...*].toArray
    let insertMany knownTrivial := params.foldl (init := knownTrivial) PersistentHashSet.insert
    withReader (fun ctx => { ctx with knownTrivial := insertMany ctx.knownTrivial }) do
      remainder.allM fun arg => do
        let argType ← Meta.inferType arg
        if ← Meta.isProp argType then
          return false
        else
          visitExpr argType
  return hasSimpleType

private partial def visitInduct (info : InductiveVal) : TrivialM Bool := do
  if (← get).visited.contains info.name then
    return true
  else
    modify fun s => { s with visited := s.visited.insert info.name }

  if info.ctors.isEmpty then return false
  if info.numIndices != 0 then return false
  if ← Meta.isPropFormerType info.type then return true

  let simplifiedType ← unfoldTypeAliases info.type
  let hasSimpleType ← Meta.forallTelescope simplifiedType fun args _ => do
    args.allM fun arg => do
      let .sort u ← Meta.inferType arg | return false
      return u.isNeverZero

  if !hasSimpleType then return false

  info.ctors.allM fun ctor => do
    let info ← getConstInfoCtor ctor
    visitCtor info

private partial def visitExpr (e : Expr) : TrivialM Bool := do
  let e ← Meta.zetaReduce e
  let e ← Core.betaReduce e
  let e ← unfoldTypeAliases e
  if (← read).knownTrivial.contains e then
    return true
  else if ← Meta.isProp e then
    return true

  match e with
  | .const .. | .app .. =>
    e.withApp fun fn args => do
      let .const name _ := fn | return false
      match ← getConstInfo name with
      | .inductInfo info =>
        if !(← visitInduct info) then return false
        args.allM visitExpr
      | .axiomInfo info =>
        if info.type.isSort then
          return true
        else
          return false
      | _ => return false
  | .forallE .. =>
    Meta.forallTelescope e fun _ dom => do
      visitExpr dom
  | _ => return false

end

/--
This function implements a heuristic for detecting whether the invariant
associated with some `Expr` `e` is going to be trivial and thus unnecessary.

The heuristic for this is roughly: If the type has at most other type arguments (i.e. no value ones)
we call it trivial if it has at least one constructor and all of its constructors bind only other
trivial types and in particular no proofs.

Using this result, if we encounter a type that is trivial and all of its argument types are trivial
as well we know for sure that its invariant is going to be useless and we can drop it.
-/
public def typeHasTrivialInvariant (e : Expr) : MetaM Bool := do
  let res ← visitExpr e |>.run {} |>.run' {}
  trace[chako.elimdep] m!"Has trivial invariant {e}? {res}"
  return res

end ElimDep
end Transformation
end Chako
