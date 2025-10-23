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
  nameIdx : Nat := 0
  freshDecls : List Declaration := []

public abbrev TransforM := ReaderT NunchakuConfig <| StateRefT TransforM.State MetaM

namespace TransforM

-- Our own sorry to avoid printing "this theorem relies on sorry"
public meta axiom sorryAx (α : Sort u) : α

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

def findEquationsForDefn (info : DefinitionVal) : MetaM (Array Expr) := do
  if ← Meta.isMatcher info.name then
    (← Match.getEquationsFor info.name).eqnNames.mapM equationTheoremType
  else
    match info.name with
    | ``dite =>
      let thm ← diteThm
      return #[thm]
    | ``Decidable.decide =>
      let thm ← decidableDecideThm
      return #[thm]
    | _ =>
      let some eqns ← getEqnsFor? info.name
        | throwError s!"Unable to find equations for {mkConst info.name}"
      eqns.mapM equationTheoremType
where
  equationTheoremType (thm : Name) : MetaM Expr := do
    inferType (← mkConstWithLevelParams thm)

  decidableDecideThm : MetaM Expr := do
    withLocalDeclD `p (mkSort 0) fun p => do
    withLocalDeclD `inst (mkApp (mkConst ``Decidable) p) fun inst => do
      let lhs := mkApp2 (mkConst ``Decidable.decide) p inst
      let rhs := mkApp5 (mkConst ``ite [1])
        (mkConst ``Bool)
        p
        (mkApp (mkConst ``Classical.propDecidable) p)
        (mkConst ``Bool.true)
        (mkConst ``Bool.false)
      let eq ← mkEq lhs rhs
      Meta.mkForallFVars #[p, inst] eq

  diteThm : MetaM Expr := do
    let u := .param `u
    withLocalDeclD `α (mkSort u) fun α => do
    withLocalDeclD `c (mkSort 0) fun c => do
    withLocalDeclD `inst (mkApp (mkConst ``Decidable) c) fun inst => do
    withLocalDeclD `t (← mkArrow c α) fun t => do
    withLocalDeclD `e (← mkArrow (mkNot c) α) fun e => do
      let lhs := mkApp5 (mkConst ``dite [u]) α c inst t e
      let rhs := mkApp5 (mkConst ``ite [u])
        α
        c
        (mkApp (mkConst ``Classical.propDecidable) c)
        (mkApp t (mkApp (mkConst ``TransforM.sorryAx [0]) c))
        (mkApp e (mkApp (mkConst ``TransforM.sorryAx [0]) (mkNot c)))
      let eq ← mkEq lhs rhs
      Meta.mkForallFVars #[α, c, inst, t, e] eq

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

public def mkFreshName (name : Name) (pref : String := "") : TransforM Name := do
  let idx := (← get).nameIdx
  modify fun s => { s with nameIdx := s.nameIdx + 1}
  return Name.str name s!"{pref}{idx}"

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

end TransforM

end Nunchaku
