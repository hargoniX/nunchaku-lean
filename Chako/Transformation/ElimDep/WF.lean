module
public import Lean.Meta.Basic
import Lean.Elab.PreDefinition.WF.GuessLex
import Lean.Elab.PreDefinition.FixedParams

/-!
This module contains an implementation of `[wf]` attribute inference for inductive types. This is
done by using the approach from "Relational Analysis of (Co)inductive Predicates, (Co)algebraic
Datatypes, and (Co)recursive Functions" (https://www.tcs.ifi.lmu.de/staff/jasmin-blanchette/sqj2013-relational.pdf)
with Lean's lexicographic guessing framework. 
-/

namespace Chako
namespace Transformation
namespace ElimDep

open Lean Meta

open Lean.Elab.WF.GuessLex
open Lean.Elab

def collectCtorRecCalls (indInfo : InductiveVal) (ctor : Name) : MetaM (Option (Array RecCallWithContext)) := do
  let info ← getConstInfoCtor ctor
  Meta.forallTelescope info.type fun args concl => do
    /-
    We are now interested in two shapes of arguments:
    1. Full applications of `ind` where `ind` doesn't appear nested anymore
    2. Arguments that do not contain `ind` at all

    We attempt to partition according to this criterion, if we find an argument
    that does not fit into either of these classes we give up.
    -/
    let mut recCalls := #[]
    let params := concl.getAppArgs
    for arg in args do
      let argType ← Meta.inferType arg
      if argType.isAppOf indInfo.name then
        let args := argType.getAppArgs
        if args.size != indInfo.numParams + indInfo.numIndices then return none
        if args.any occursCheck then return none
        recCalls := recCalls.push (← mkRecCall params args)
      else
        if occursCheck argType then return none

    return some recCalls
where
  mkRecCall (params : Array Expr) (args : Array Expr) : MetaM RecCallWithContext := do
    RecCallWithContext.create .missing 0 params 0 args

  occursCheck (expr : Expr) : Bool :=
    expr.find? (Expr.isConstOf · indInfo.name) |>.isSome

def collectInductiveRecCalls (info : InductiveVal) : MetaM (Option (Array RecCallWithContext)) := do
  let mut calls := #[]
  for ctor in info.ctors do
    let some additionalCalls ← collectCtorRecCalls info ctor | return none
    calls := calls ++ additionalCalls
  return some calls

def collectFixedParams (info : InductiveVal) (predef : PreDefinition) : MetaM FixedParamPerms := do
  -- We approximate the fixed parameters as the parameters of the inductive type
  let mut perms := info.numParams.fold (init := Array.emptyWithCapacity info.numParams)
    fun i _ acc => acc.push (some i)
  perms := perms ++ Array.replicate info.numIndices none
  let revDeps ← getParamRevDeps predef.value
  return {
    numFixed := info.numParams
    perms := #[perms]
    revDeps := #[revDeps]
  }

/--
We rely on the invariant promised by the original `guessLex`: The only thing of this pre definition
that matters is the lambda header of the body.
-/
def fakePreDefinition (info : InductiveVal) : MetaM Elab.PreDefinition := do
  let body ← Meta.forallTelescope info.type fun args _ => do
    Meta.mkLambdaFVars args (mkConst ``True)
  return {
    ref := .missing
    kind := .def
    levelParams := info.levelParams
    modifiers := {}
    declName := info.name
    binders := .missing
    type := info.type
    value := body
    termination := {
      ref := .missing
      terminationBy?? := none
      terminationBy? := none
      partialFixpoint? := none
      decreasingBy? := none
      extraParams := 0
    }
  }

/-
Taken from `Lean.Elab.WF.guessLex` with modifications to handle our inductive use case.
-/
def guessLex (info : InductiveVal) : MetaM Bool := do
  let preDefs := #[← fakePreDefinition info]

  let fixedParamPerms ← collectFixedParams info preDefs[0]!
  let argsPacker : ArgsPacker := { varNamess := #[Array.replicate info.numIndices .anonymous] }
  let userVarNamess ← argsPacker.varNamess.mapM (naryVarNames ·)

  let some recCalls ← collectInductiveRecCalls info | return false
  let recCalls := filterSubsumed recCalls

  let basicMeasures₁ ← simpleMeasures preDefs fixedParamPerms userVarNamess
  let basicMeasures₂ ← complexMeasures preDefs fixedParamPerms userVarNamess recCalls
  let basicMeasures := Array.zipWith (· ++ ·) basicMeasures₁ basicMeasures₂

  let mutualMeasures ← generateMeasures (basicMeasures.map (·.size))

  let rcs ← recCalls.mapM (RecCallCache.mk #[info.name] #[none] basicMeasures ·)
  let callMatrix := rcs.map (inspectCall ·)

  let solutions? ← solve mutualMeasures callMatrix
  return solutions?.isSome

public def inductiveIsWf (info : InductiveVal) : CoreM Bool := do
  -- We must isolate this function from the context we are coming from
  MetaM.run' <|
  withTraceNode `chako.elimdep.wf (fun ret => return m!"Checking wf for {info.name}: {ret.toOption}") do
    if info.all.length > 1 then return false
    if !(← Meta.isPropFormerType info.type) then
      throwError m!"WF inference called on non prop inductive: {info.name}"

    guessLex info

end ElimDep
end Transformation
end Chako
