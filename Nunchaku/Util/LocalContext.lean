module

public import Lean.Meta.Basic
public import Lean.Meta.Tactic.FVarSubst
import Lean.Meta.Tactic.Util

namespace Nunchaku

open Lean Meta

@[inline]
partial def mapLCtx [MonadControlT MetaM m] [MonadLiftT MetaM m] [MonadError m] [Monad m]
    (lctx : LocalContext) (f : Expr → FVarSubst → m Expr) (processLetDecl : Bool) :
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
          let newType ← f decl.type subst
          withLocalDecl decl.userName decl.binderInfo newType fun newDecl =>
            go (idx + 1) oldLCtx (subst.insert decl.fvarId newDecl) f
      | some decl@(.ldecl ..) =>
        if decl.isLet && !processLetDecl then
          throwError m!"Let decls not supported"
        else
          let newType ← f decl.type subst
          withLocalDecl decl.userName decl.binderInfo newType fun newDecl =>
            go (idx + 1) oldLCtx (subst.insert decl.fvarId newDecl) f
      | none => go (idx + 1) oldLCtx subst f
    else
      let lctx ← (getLCtx (m := MetaM))
      let newLCtx := subst.domain.foldl (init := lctx) LocalContext.erase
      return (newLCtx, subst)

@[inline]
partial def mapExtendLCtx [MonadControlT MetaM m] [MonadLiftT MetaM m] [MonadError m] [Monad m]
    (lctx : LocalContext) (mapper : Expr → FVarSubst → m Expr)
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
          let origType := decl.type
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

@[specialize]
public def mapMVarId [MonadControlT MetaM m] [MonadLiftT MetaM m] [MonadError m] [MonadLCtx m]
    [Monad m] (g : MVarId) (f : Expr → FVarSubst → m Expr) (processLetDecl : Bool := false) : m MVarId :=
  g.withContext do
    let (newLCtx, subst) ← mapLCtx (← getLCtx) f processLetDecl
    let newType ← f (← g.getType) subst
    Meta.withLCtx' newLCtx do
      let g := (← Lean.Meta.mkFreshExprMVar newType).mvarId!
      return g

@[specialize]
public def mapExtendMVarId [MonadControlT MetaM m] [MonadLiftT MetaM m] [MonadError m] [MonadLCtx m]
    [Monad m] (g : MVarId) (mapper : Expr → FVarSubst → m Expr)
    (extender : Expr → FVarSubst → FVarId → m (Option Expr)) : m MVarId :=
  g.withContext do
    let (newLCtx, subst) ← mapExtendLCtx (← getLCtx) mapper extender
    let newType ← mapper (← g.getType) subst
    Meta.withLCtx' newLCtx do
      let g := (← Lean.Meta.mkFreshExprMVar newType).mvarId!
      return g

end Nunchaku
