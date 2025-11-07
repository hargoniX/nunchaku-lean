module

public import Lean.Meta.Basic
public import Lean.Meta.Tactic.FVarSubst
import Lean.Meta.Tactic.Util

/-!
This module contains infrastructure for mapping a transformation through an entire local context.
This is useful when we are transforming a goal and want to transform both the statement as well as
all of the local variables.
-/

namespace Chako

open Lean Meta

@[inline]
partial def mapLCtx [MonadControlT MetaM m] [MonadLiftT MetaM m] [MonadError m] [Monad m]
    [MonadMCtx m] (lctx : LocalContext) (f : Expr → FVarSubst → m Expr) (processLetDecl : Bool) :
    m (LocalContext × FVarSubst) := do
  go 0 lctx {} f
where
  @[specialize]
  go (idx : Nat) (oldLCtx : LocalContext) (subst : FVarSubst) (f : Expr → FVarSubst → m Expr) :
      m (LocalContext × FVarSubst) := do
    if h : idx < oldLCtx.decls.size then
      let decl := oldLCtx.decls[idx]
      match decl with
      | some decl@(.cdecl ..) =>
        if decl.isImplementationDetail then
          go (idx + 1) oldLCtx subst f
        else
          let declType ← instantiateMVars decl.type
          let newType ← f declType subst
          withLocalDecl decl.userName decl.binderInfo newType fun newDecl =>
            go (idx + 1) oldLCtx (subst.insert decl.fvarId newDecl) f
      | some decl@(.ldecl ..) =>
        if decl.isLet && !processLetDecl then
          throwError m!"Let decls not supported"
        else
          let declType ← instantiateMVars decl.type
          let newType ← f declType subst
          withLocalDecl decl.userName decl.binderInfo newType fun newDecl =>
            go (idx + 1) oldLCtx (subst.insert decl.fvarId newDecl) f
      | none => go (idx + 1) oldLCtx subst f
    else
      let lctx ← (getLCtx (m := MetaM))
      let newLCtx := subst.domain.foldl (init := lctx) LocalContext.erase
      return (newLCtx, subst)

@[inline]
partial def mapExtendLCtx [MonadControlT MetaM m] [MonadLiftT MetaM m] [MonadError m] [Monad m]
    [MonadMCtx m] (lctx : LocalContext) (mapper : Expr → FVarSubst → m Expr)
    (extender : Expr → FVarSubst → FVarId → m (Option Expr)) : m (LocalContext × FVarSubst) :=
  go 0 lctx {}
where
  @[specialize]
  go (idx : Nat) (oldLCtx : LocalContext) (subst : FVarSubst) : m (LocalContext × FVarSubst) := do
    if h : idx < oldLCtx.decls.size then
      let decl := oldLCtx.decls[idx]
      match decl with
      | some decl@(.cdecl ..) =>
        if decl.isImplementationDetail then
          go (idx + 1) oldLCtx subst
        else
          let origType ← instantiateMVars decl.type
          let newType ← mapper origType subst
          withLocalDecl decl.userName decl.binderInfo newType fun newDecl => do
            if let some additional ← extender origType subst newDecl.fvarId! then
              withLocalDecl `h .default additional fun _ => do
                go (idx + 1) oldLCtx (subst.insert decl.fvarId newDecl)
            else
              go (idx + 1) oldLCtx (subst.insert decl.fvarId newDecl)
      | some (.ldecl ..) => throwError m!"Let decls not supported"
      | none => go (idx + 1) oldLCtx subst
    else
      let lctx ← (getLCtx (m := MetaM))
      let newLCtx := subst.domain.foldl (init := lctx) LocalContext.erase
      return (newLCtx, subst)

/--
Map a transformation `f` over a goal `g`, transforming all the local assumptions as well as the
theorem statement. `f` takes both a type/prop to transform as well as a substitution from original
fvars to their transformed counterpart.
-/
@[specialize]
public def mapMVarId [MonadControlT MetaM m] [MonadLiftT MetaM m] [MonadError m] [MonadLCtx m]
    [MonadMCtx m] [Monad m] (g : MVarId) (f : Expr → FVarSubst → m Expr)
    (processLetDecl : Bool := false) : m MVarId :=
  g.withContext do
    let (newLCtx, subst) ← mapLCtx (← getLCtx) f processLetDecl
    let gType ← instantiateMVars (← g.getType)
    let newType ← f gType subst
    Meta.withLCtx' newLCtx do
      let g := (← Lean.Meta.mkFreshExprMVar newType).mvarId!
      return g

/--
Like `mapMVarId` but `extender` can additionally be used to add additional assumptions into the
local context as we transform. For this purpose it is called on all local assumptions and
takes the original type/prop, the same substitution as the `mapper` and the `FVarId` of the already
transformed declaration it is currently operating on.
-/
@[specialize]
public def mapExtendMVarId [MonadControlT MetaM m] [MonadLiftT MetaM m] [MonadError m]
    [MonadLCtx m] [MonadMCtx m] [Monad m] (g : MVarId) (mapper : Expr → FVarSubst → m Expr)
    (extender : Expr → FVarSubst → FVarId → m (Option Expr)) : m MVarId :=
  g.withContext do
    let (newLCtx, subst) ← mapExtendLCtx (← getLCtx) mapper extender
    let gType ← instantiateMVars (← g.getType)
    let newType ← mapper gType subst
    Meta.withLCtx' newLCtx do
      let g := (← Lean.Meta.mkFreshExprMVar newType).mvarId!
      return g

end Chako
