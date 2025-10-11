module

public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.Model

/-!
This module contains the transformation for abstracting free variables that are types formers into
into axioms in order to enable specialisations of types that depend on free variables.
-/

namespace Nunchaku
namespace Transformation
namespace AbstractTypes

open Lean

public def transformation : Transformation Lean.MVarId Lean.MVarId LeanResult LeanResult where
  st := private Unit
  inner := private {
    name := "Abstract Types"
    encode g := g.withContext do
      let mut subst : Std.HashMap FVarId Expr := {}
      for decl in ← getLCtx do
        if decl.isImplementationDetail then
          continue
        let fvar := decl.fvarId
        if (← fvar.getType) matches .sort (.succ ..) then
          trace[nunchaku.abstract] m!"Going to abstract {mkFVar fvar}"
          let name ← mkAuxDeclName (← fvar.getUserName)
          let axiomDecl := {
            name,
            levelParams := [],
            type := (← decl.fvarId.getType),
            isUnsafe := false
          }
          addDecl <| .axiomDecl axiomDecl
          subst := subst.insert decl.fvarId (mkConst name [])

      let newLCtx := subst.fold (init := ← getLCtx) (fun lctx fvar ax => lctx.replaceFVarId fvar ax)
      let (fvars, vs) := subst.fold (init := (#[], #[]))
        fun (fvars, vs) fvar ax => (fvars.push (mkFVar fvar), vs.push ax)
      let newType := (← g.getType).replaceFVars fvars vs
      -- TODO: Possibly think about local instances
      Meta.withLCtx' newLCtx do
        let g := (← Meta.mkFreshExprMVar (some newType) .natural g.name).mvarId!
        trace[nunchaku.abstract] m!"Result: {g}"
        return (g, ())
    decode _ res := return res
  }

end AbstractTypes
end Transformation
end Nunchaku
