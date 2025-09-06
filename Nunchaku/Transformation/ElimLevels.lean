import Nunchaku.Util.Pipeline
import Nunchaku.Util.Model
import Nunchaku.Util.LocalContext

namespace Nunchaku
namespace Transformation
namespace ElimLevels

open Lean

def elimLevelParams (e : Expr) (subst : Meta.FVarSubst) : TransforM Expr := do
  let out ← Core.transform e (post := post subst)
  return out
where
  post (subst : Meta.FVarSubst) (e : Expr) : TransforM TransformStep := do
    match e with
    | .sort u =>
      return .done <| .sort <| killParams u
    | .const name us =>
      return .done <| .const name (us.map killParams)
    | .fvar .. => return .done <| subst.apply e
    | _ => return .continue

  killParams (l : Level) : Level :=
    l.substParams (fun _ => some 0) |>.normalize

def transformation : Transformation MVarId MVarId LeanResult LeanResult where
   st := Unit
   inner := {
    name := "ElimLevels"
    encode g := g.withContext do
      let g ← mapMVarId g elimLevelParams
      trace[nunchaku.elimlevels] m!"Result: {g}"
      return (g, ())
    decode _ res := return res
  }

end ElimLevels
end Transformation
end Nunchaku
