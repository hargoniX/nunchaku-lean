module

import Lean.Meta.Eqns
import Lean.Meta.Reduce
public import Chako.Attr
public meta import Chako.Attr -- TODO: this should not be necessary
import Lean.Meta.Match.MatchEqsExt
import Chako.Util.AuxiliaryConsts
public import Chako.Util.NunchakuSyntax

/-!
This module contains the definition of the `TransforM` monad which is the core
monad that almost all operations of the Chako tactic operate in.
-/

namespace Chako

open Lean Meta

public structure TransforM.State where
  equations : Std.HashMap Name (List Expr)
  nameIdx : Nat := 0
  freshDecls : List Declaration := []
  attributes : Std.HashMap Lean.Name (Std.TreeSet NunAttribute) := {}

public abbrev TransforM := ReaderT ChakoConfig <| StateRefT TransforM.State MetaM

namespace TransforM

-- Our own sorry to avoid printing "this theorem relies on sorry"
public meta axiom sorryAx (α : Sort u) : α

public def mkSorryAx (ty : Expr) (lvl : Level) : Expr :=
  mkApp (mkConst ``sorryAx [lvl]) ty

def builtins : Std.HashSet Name :=
  .ofList [``True, ``False, ``Not, ``And, ``Or, ``Eq, ``Ne, ``Iff, ``Exists,
    ``Chako.classicalIf]

public def isBuiltin (n : Name) : Bool := builtins.contains n

public def getConfig : TransforM ChakoConfig := do return (← read)

public def getEquations : TransforM (Std.HashMap Name (List Expr)) := do
  return (← get).equations

public def getEquationsFor (decl : Name) : TransforM (List Expr) := do
  return (← get).equations.getD decl []

public def injectEquations (decl : Name) (eqs : List Expr) : TransforM Unit := do
  if (← get).equations.contains decl then
    throwError m!"Trying to inject equations for already existing decl {decl}"
  else
    modify fun s => { s with equations := s.equations.insert decl eqs }

public def replaceEquations (equations : Std.HashMap Name (List Expr)) : TransforM Unit :=
  modify fun s => { s with equations }

public def preprocessEquation (eq : Expr) : MetaM Expr := do
  Meta.forallTelescope eq fun args body => do
    let mkApp3 (.const ``Eq [u]) α lhs rhs := body | throwError m!"Equation is malformed: {eq}"
    let fnArgs := lhs.getAppArgs
    let fnArgs ← fnArgs.mapM Meta.reduce
    let lhs := mkAppN lhs.getAppFn fnArgs
    let body := mkApp3 (.const ``Eq [u]) α lhs rhs
    Meta.mkForallFVars args body


public def equationIsNonTrivial (eq : Expr) : MetaM Bool := do
  /-
  For now our simple criterion is: If anything in the ∀ binder on the beginning of the equation
  does not occur in the body we know we cannot translate it to nunchaku for sure and should
  instead use the definition as the equation
  -/
  Meta.forallTelescope eq fun args body => do
    let args := args.map Expr.fvarId!
    return !args.all body.containsFVar

def findEquationsForDefn (info : DefinitionVal) : MetaM (Array Expr) := do
  if (← Meta.isMatcher info.name) || (isCasesOnRecursor (← getEnv) info.name) then
    return #[]
  else
    let some eqns ← getEqnsFor? info.name
      | throwError m!"Unable to find equations for {mkConst info.name}"
    let eqns ← eqns.mapM fun thm => do inferType (← mkConstWithLevelParams thm)
    if ← eqns.anyM equationIsNonTrivial then
      let some unfoldThm ← getUnfoldEqnFor? (nonRec := true) info.name
        | throwError m!"Unable to find unfold equation for {info.name}"
      let eq ← inferType (← mkConstWithLevelParams unfoldThm)
      return #[eq]
    else
      return eqns

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
    trace[chako.equations] m!"Working {elem}"
    let constInfo ← getConstInfo elem
    match constInfo with
    | .defnInfo info =>
      -- A theorem in disguise!
      if ← Meta.isProof (← mkConstWithLevelParams constInfo.name) then
        let used := constInfo.type.getUsedConstants
        worklist := worklist ++ used
        continue
      else
        let eqns ← findEquationsForDefn info
        let eqns ← eqns.mapM preprocessEquation
        defs := defs.insert elem eqns.toList
        for eq in eqns do
          let used := eq.getUsedConstants
          let used := used.filter (fun n => !visited.contains n)
          worklist := worklist ++ used
    | .inductInfo .. | .axiomInfo .. | .opaqueInfo .. | .recInfo .. | .ctorInfo .. =>
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

public def mkFreshName (name : Name) (pref : String := "") : TransforM Name := do
  let idx := (← get).nameIdx
  modify fun s => { s with nameIdx := s.nameIdx + 1}
  return Name.str name s!"{pref}{idx}"

public def run (g : MVarId) (cfg : ChakoConfig) (x : TransforM α) : MetaM α := do
  let equations ←
    withTraceNode `chako.equations (fun _ => return m!"Looking for equations") do
      findEquations g
  withTraceNode `chako.equations (fun _ => return m!"Collected Equations") do
    for (name, eqns) in equations do
      trace[chako.equations] m!"- {name}"
      for eq in eqns do
        trace[chako.equations] m!"  - {eq}"

  StateRefT'.run' (ReaderT.run x cfg) { equations }

end TransforM

end Chako
