import Nunchaku.Util.Pipeline
import Nunchaku.Util.Model

namespace Nunchaku
namespace Transformation
namespace ElimLevels

open Lean

def elimLevelParams (e : Expr) : TransforM Expr := do
  let out ← Core.transform e (post := post)
  return out
where
  post (e : Expr) : TransforM TransformStep := do
    match e with
    | .sort u =>
      return .done <| .sort <| killParams u
    | .const name us =>
      return .done <| .const name (us.map killParams)
    | _ => return .continue

  killParams (l : Level) : Level :=
    l.substParams (fun _ => some 0) |>.normalize

def transformation : Transformation MVarId MVarId LeanResult LeanResult where
   st := Unit
   inner := {
    name := "ElimLevels"
    encode g := g.withContext do
      let origLCtx ← getLCtx
      let mut newLCtx := origLCtx
      for decl in origLCtx do
        if decl.isImplementationDetail then
          continue
        if decl.isLet then
          throwError "Unsupported: let decls"

        let fvar := decl.fvarId
        let type ← fvar.getType
        let newType ← elimLevelParams type
        newLCtx := newLCtx.modifyLocalDecl decl.fvarId fun decl =>
          match decl with
          | .cdecl idx fvar name _ bi kind =>
            .cdecl idx fvar name newType bi kind
          | _ => unreachable!

      let origType ← g.getType
      let newType ← elimLevelParams origType

      -- TODO: Possibly think about local instances
      Meta.withLCtx' newLCtx do
        let g := (← Meta.mkFreshExprMVar (some newType) .natural g.name).mvarId!
        let equations ← TransforM.getEquations
        let mut newEquations := {}
        for (name, eqs) in equations do
          let newEqs ← eqs.mapM elimLevelParams
          newEquations := newEquations.insert name newEqs
        TransforM.replaceEquations newEquations
        trace[nunchaku.elimlevels] m!"Result: {g}"
        return (g, ())

    decode _ res := return res
  }

end ElimLevels
end Transformation
end Nunchaku
