module

public import Chako.Util.Pipeline
public import Chako.Util.Model
import Chako.Util.LocalContext
import Chako.Util.AddDecls
import Chako.Util.Funext
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Intro

namespace Chako
namespace Transformation
namespace ElimComfort

open Lean

structure ComfortState where
  consts : Std.HashMap Name Name := {}

abbrev ComfortM := StateRefT ComfortState TransforM

def ComfortM.run (x : ComfortM α) : TransforM α :=
  StateRefT'.run' x {}

def zetaBetaReduce (e : Expr) : MetaM Expr := do
  let e ← Meta.zetaReduce e
  Core.betaReduce e

/--
This function eliminates:
- universe parameters by instanting them with 1
- applies ζ and β reduction
-/
def elimComfortUniv (e : Expr) (subst : Meta.FVarSubst) : ComfortM Expr := do
  let e ← zetaBetaReduce e
  let e ← Util.funextTransform e true
  Meta.transform e (pre := pre)
where
  pre (e : Expr) : ComfortM TransformStep := do
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
    | .param _ => 1
    | .mvar .. => unreachable!

def encode (g : MVarId) : ComfortM MVarId := g.withContext do
  mapMVarId g elimComfortUniv (processLetDecl := true)

public def transformation : Transformation MVarId MVarId NunResult NunResult where
   st := Unit
   inner := {
    name := "ElimComfort"
    encode g := do
      let g ← ComfortM.run <| encode g
      let (_, g) ← g.intros
      trace[chako.elimcomfort] m!"Result: {g}"
      return (g, ())
    decode _ res := return res
  }

end ElimComfort
end Transformation
end Chako
