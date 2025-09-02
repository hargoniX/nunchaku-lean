import Lean.Meta.Match.MatchEqsExt
import Nunchaku.Attr

/-!
This module contains the definition of the `TransforM` monad which is the core
monad that almost all operations of the Nunchaku tactic operate in.
-/

namespace Nunchaku

open Lean Meta

structure TransforM.State where
  equations : Std.HashMap Name (List Expr)

abbrev TransforM := ReaderT NunchakuConfig <| StateRefT TransforM.State MetaM

namespace TransforM

private def builtins : Std.HashSet Name :=
  .ofList [``True, ``False, ``Not, ``And, ``Or, ``Eq, ``Ne, ``Iff, ``ite, ``Exists]

def isBuiltin (n : Name) : Bool := builtins.contains n

def getConfig : TransforM NunchakuConfig := do return (← read)

def getEquations : TransforM (Std.HashMap Name (List Expr)) := do
  return (← get).equations

def getEquationsFor (decl : Name) : TransforM (List Expr) := do
  return (← get).equations.getD decl []

def replaceEquations (equations : Std.HashMap Name (List Expr)) : TransforM Unit :=
  modify fun s => { s with equations }

private def findEquations (g : MVarId) : MetaM (Std.HashMap Name (List Expr)) := do
  let mut worklist : Array Name ← initializeWorklist g
  let mut defs : Std.HashMap Name (List Expr) := {}
  let mut visited : Std.HashSet Name := {}
  while !worklist.isEmpty do
    let elem := worklist.back!
    worklist := worklist.pop
    if visited.contains elem || isBuiltin elem then
      continue
    visited := visited.insert elem
    let constInfo ← getConstInfo elem
    -- HACK
    if constInfo.isDefinition && elem != ``rfl then
      let some eqns ← getEqnsFor? elem | throwError s!"Unable to find equations for {mkConst elem}"
      let eqns ← eqns.mapM fun eq => do inferType (← mkConstWithLevelParams eq)
      defs := defs.insert elem eqns.toList
      for eq in eqns do
        let used := eq.getUsedConstantsAsSet
        for name in used do
          if visited.contains name then
            continue
          worklist := worklist.push name
    else
      let used := constInfo.type.getUsedConstantsAsSet
      for name in used do
        if visited.contains name || isBuiltin name then
          continue
        worklist := worklist.push name

  return defs
where
  initializeWorklist (g : MVarId) : MetaM (Array Name) := g.withContext do
    let mut used := (← g.getType).getUsedConstants
    for decl in ← getLCtx do
      if decl.isImplementationDetail then
        continue
      if decl.isLet then
        throwError "Unsupported: let decls"
      used := used ++ decl.type.getUsedConstants
    return used

def run (g : MVarId) (cfg : NunchakuConfig) (x : TransforM α) : MetaM α := do
  let equations ← findEquations g
  trace[nunchaku.equations] "Collected equations:"
  for (name, eqns) in equations do
    trace[nunchaku.equations] m!"- {name}"
    for eq in eqns do
      trace[nunchaku.equations] m!"  - {eq}"

  StateRefT'.run' (ReaderT.run x cfg) { equations }

end TransforM

end Nunchaku
