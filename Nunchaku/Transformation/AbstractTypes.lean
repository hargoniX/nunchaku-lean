import Nunchaku.Util.Pipeline
import Nunchaku.Util.Model

/-!
This module contains the transformation for abstracting free variables that are type formers into
axioms in order to enable specialisations of types that depend on free variables.
-/

namespace Nunchaku
namespace Transformation
namespace AbstractTypes

open Lean
/-
          let levelParams := collectLevelParams {} (← decl.fvarId.getType) |>.params |>.toList
          let name := sorry
          let axiomDecl := {
            name,
            levelParams,
            type := (← decl.fvarId.getType),
            isUnsafe := true
          }
          addDecl <| .axiomDecl axiomDecl
          -/

def transformation : Transformation Lean.MVarId Lean.MVarId LeanResult LeanResult where
  st := Unit
  inner := {
    name := "Abstract Types"
    encode g := g.withContext do
      -- TODO: Need to handle situations in which the type former depends on a local type
      let mut subst : Std.HashMap FVarId Expr := {}
      for decl in ← getLCtx do
        if decl.isImplementationDetail then
          continue
        if decl.isLet then
          throwError "Unsupported: let decls"
        let fvar := decl.fvarId
        if ← Meta.isTypeFormer (mkFVar fvar) then
          trace[nunchaku.abstract] m!"Going to abstract {mkFVar fvar}"
          let levelParams := collectLevelParams {} (← fvar.getType) |>.params |>.toList
          let name ← mkAuxDeclName (← fvar.getUserName)
          let axiomDecl := {
            name,
            levelParams,
            type := (← decl.fvarId.getType),
            isUnsafe := false
          }
          addDecl <| .axiomDecl axiomDecl
          subst := subst.insert decl.fvarId (mkConst name (levelParams.map .param))

      let newLCtx := subst.fold (init := ← getLCtx) (fun lctx fvar ax => lctx.replaceFVarId fvar ax)
      let (fvars, vs) := subst.fold (init := (#[], #[]))
        fun (fvars, vs) fvar ax => (fvars.push (mkFVar fvar), vs.push ax)
      let newType := (← g.getType).replaceFVars fvars vs
      -- TODO: Possibly think about local instances
      Meta.withLCtx' newLCtx do
        let g ← Meta.mkFreshExprMVar (some newType) .natural g.name
        return (g.mvarId!, ())
    decode _ res := return res
  }

end AbstractTypes
end Transformation
end Nunchaku
