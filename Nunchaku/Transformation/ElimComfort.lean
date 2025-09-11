module

public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.Model
import Nunchaku.Util.LocalContext
import Lean.Meta.Tactic.Clear

/-!
This module contains the transformation for eliminating comfort features from Lean, in particular:
- universe parameters by instantiating them with `0`
- let declarations by ζ reduction
- lambdas by lambda lifting TODO

TODO: currently this is only done in the goal and in equations, we might also need to do this in
other type definitions

TODO: right before emitting the raw problem to nunchaku we might be better of globally sharing with
lets so we don't produce an exponential problem.
-/

namespace Nunchaku
namespace Transformation
namespace ElimComfort

open Lean

def zetaBetaReduce (e : Expr) : TransforM Expr := do
  let e ← Meta.zetaReduce e
  Core.betaReduce e

/--
This function eliminates universe parameters by instanting them with `0` and in the same traversal
applies ζ and β reduction.
-/
def elimUnivZetaBetaReduce (e : Expr) (subst : Meta.FVarSubst) : TransforM Expr := do
  let e ← zetaBetaReduce e
  Meta.transform e (pre := pre subst)
where
  pre (subst : Meta.FVarSubst) (e : Expr) : TransforM TransformStep := do
    match e with
    | .sort u =>
      return .done <| .sort <| killParams u
    | .const name us =>
      return .done <| .const name (us.map killParams)
    | .fvar .. => return .done <| subst.apply e
    | _ => return .continue

  killParams (l : Level) : Level :=
    Level.ofNat <| killParamsAux l

  killParamsAux (l : Level) : Nat :=
    match l with
    | .zero => 0
    | .succ l => killParamsAux l + 1
    | .max l r => max (killParamsAux l) (killParamsAux r)
    | .imax l r =>
      let r := killParamsAux r
      if r == 0 then
        0
      else
        max (killParamsAux l) r
    | .param _ => 0
    | .mvar .. => unreachable!

public def transformation : Transformation MVarId MVarId LeanResult LeanResult where
   st := private Unit
   inner := private {
    name := "ElimComfort"
    encode g := g.withContext do
      let g ← mapMVarId g elimUnivZetaBetaReduce (processLetDecl := true)
      g.withContext do
        let mut lets := #[]
        for decl in ← getLCtx do
          if decl.isImplementationDetail then
            continue
          if decl.isLet then
            lets := lets.push decl.fvarId
        let g ← g.tryClearMany lets

        let equations ← TransforM.getEquations
        let mut newEquations := {}
        for (name, eqs) in equations do
          let eqs ← eqs.mapM zetaBetaReduce
          newEquations := newEquations.insert name eqs
        TransforM.replaceEquations newEquations
        trace[nunchaku.elimcomfort] m!"Result: {g}"
        return (g, ())
    decode _ res := return res
  }

end ElimComfort
end Transformation
end Nunchaku
