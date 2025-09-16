module

import Lean.Meta.Eqns
import Lean.Meta.Reduce
public import Nunchaku.Attr
public meta import Nunchaku.Attr -- TODO: this should not be necessary
import Lean.Meta.Match.MatchEqsExt

/-!
This module contains the definition of the `TransforM` monad which is the core
monad that almost all operations of the Nunchaku tactic operate in.
-/

namespace Nunchaku

open Lean Meta

public structure TransforM.State where
  equations : Std.HashMap Name (List Expr)

public abbrev TransforM := ReaderT NunchakuConfig <| StateRefT TransforM.State MetaM

namespace TransforM

def builtins : Std.HashSet Name :=
  .ofList [``True, ``False, ``Not, ``And, ``Or, ``Eq, ``Ne, ``Iff, ``ite, ``Exists]

public def isBuiltin (n : Name) : Bool := builtins.contains n

public def getConfig : TransforM NunchakuConfig := do return (← read)

public def getEquations : TransforM (Std.HashMap Name (List Expr)) := do
  return (← get).equations

public def getEquationsFor (decl : Name) : TransforM (List Expr) := do
  return (← get).equations.getD decl []

public def replaceEquations (equations : Std.HashMap Name (List Expr)) : TransforM Unit :=
  modify fun s => { s with equations }

def preprocessEquation (eq : Expr) : MetaM Expr := do
  Meta.forallTelescope eq fun args body => do
    let mkApp3 (.const ``Eq [u]) α lhs rhs := body | throwError m!"Equation is malformed: {eq}"
    let fnArgs := lhs.getAppArgs
    let fnArgs ← fnArgs.mapM Meta.reduce
    let lhs := mkAppN lhs.getAppFn fnArgs
    let body := mkApp3 (.const ``Eq [u]) α lhs rhs
    Meta.mkForallFVars args body

def findEquations (g : MVarId) : MetaM (Std.HashMap Name (List Expr)) := do
  let mut worklist : Array Name ← initializeWorklist g
  let mut defs : Std.HashMap Name (List Expr) := {}
  let mut visited : Std.HashSet Name := {}
  while !worklist.isEmpty do
    let elem := worklist.back!
    worklist := worklist.pop
    if visited.contains elem || isBuiltin elem then
      continue
    visited := visited.insert elem
    trace[nunchaku.equations] m!"Working {elem}"
    let constInfo ← getConstInfo elem
    match constInfo with
    | .defnInfo .. =>
      -- A theorem in disguise!
      if ← Meta.isProof (← mkConstWithLevelParams constInfo.name) then
        let used := constInfo.type.getUsedConstants
        worklist := worklist ++ used
        continue
      else
        let eqns ←
          if ← Meta.isMatcher constInfo.name then
            pure (← Match.getEquationsFor constInfo.name).eqnNames
          else
            let some eqns ← getEqnsFor? elem | throwError s!"Unable to find equations for {mkConst elem}"
            pure eqns
        let eqns ← eqns.mapM fun eq => do inferType (← mkConstWithLevelParams eq)
        let eqns ← eqns.mapM preprocessEquation
        defs := defs.insert elem eqns.toList
        for eq in eqns do
          let used := eq.getUsedConstants
          worklist := worklist ++ used
    | .inductInfo .. | .axiomInfo .. | .opaqueInfo .. | .recInfo .. | .ctorInfo .. =>
      -- TODO: Don't traverse into theorems here
      let used := constInfo.getUsedConstantsAsSet.toArray
      worklist := worklist ++ used
    | .thmInfo info =>
      let used := info.type.getUsedConstantsAsSet.toArray
      worklist := worklist ++ used
    | .quotInfo .. => throwError "No quotient support"

  return defs
where
  initializeWorklist (g : MVarId) : MetaM (Array Name) := g.withContext do
    let mut used := (← g.getType).getUsedConstants
    for decl in ← getLCtx do
      if decl.isImplementationDetail then
        continue
      used := used ++ decl.type.getUsedConstants ++ (decl.value?.map Expr.getUsedConstants).getD #[]
    return used

public def run (g : MVarId) (cfg : NunchakuConfig) (x : TransforM α) : MetaM α := do
  let equations ←
    withTraceNode `nunchaku.equations (fun _ => return m!"Looking for equations") do
      findEquations g
  withTraceNode `nunchaku.equations (fun _ => return m!"Collected Equations") do
    for (name, eqns) in equations do
      trace[nunchaku.equations] m!"- {name}"
      for eq in eqns do
        trace[nunchaku.equations] m!"  - {eq}"

  StateRefT'.run' (ReaderT.run x cfg) { equations }


-- Our own sorry to avoid printing "this theorem relies on sorry"
public meta axiom sorryAx (α : Sort u) : α

end TransforM

end Nunchaku
