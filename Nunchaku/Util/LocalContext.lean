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

@[specialize f]
public def mapMVarId [MonadControlT MetaM m] [MonadLiftT MetaM m] [MonadError m] [MonadLCtx m]
    [Monad m] (g : MVarId) (f : Expr → FVarSubst → m Expr) (processLetDecl : Bool := false) : m MVarId :=
  g.withContext do
    let (newLCtx, subst) ← mapLCtx (← getLCtx) f processLetDecl
    let newType ← f (← g.getType) subst
    Meta.withLCtx' newLCtx do
      let g := (← Lean.Meta.mkFreshExprMVar newType).mvarId!
      return g

end Nunchaku
