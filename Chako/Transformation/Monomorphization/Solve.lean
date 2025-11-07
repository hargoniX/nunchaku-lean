module

public import Chako.Transformation.Monomorphization.Util
import Lean.Util.SCC

namespace Chako
namespace Transformation
namespace Monomorphization
namespace Solve

open Lean

structure Node where
  var : FlowVariable
  idx : Nat
deriving BEq, Hashable, Repr

structure Edge where
  node : Node
  growing : Bool
deriving BEq, Hashable, Repr

structure ConstraintGraph where
  nodes : Std.HashSet Node := {}
  edges : Std.HashMap Node (Std.HashSet Edge) := {}

namespace ConstraintGraph

abbrev M := StateT ConstraintGraph (ReaderT MonoAnalysisState Id)

partial def ofConstraints (constraints : List FlowConstraint) (mono : MonoAnalysisState) :
    ConstraintGraph :=
  let (_, g) := go constraints |>.run {} |>.run mono
  g
where
  go (constraints : List FlowConstraint) : M Unit :=
    constraints.forM fun constraint => do
      match constraint.src with
      | .var srcVar =>
        let varSize ← getVarSize srcVar
        for idx in 0...varSize do
          addEdge { var := srcVar, idx } false { var := constraint.dst, idx }
      | .vec args =>
        for h : idx in 0...args.size do
          handleArg args[idx] constraint.dst idx

  getVarSize (var : FlowVariable) : M Nat := do
    return (← read).argPos[var.function]!.size

  handleArg (arg : FlowTypeArg) (dst : FlowVariable) (dstIdx : Nat) : M Unit := do
    match arg with
    | .index src srcIdx => addEdge { var := src, idx := srcIdx } false { var := dst, idx := dstIdx }
    | .const name innerArgs => innerArgs.forM (handleInnerArg · dst dstIdx)
    | .func dom codom =>
      handleInnerArg dom dst dstIdx
      handleInnerArg codom dst dstIdx

  handleInnerArg (arg : FlowTypeArg) (dst : FlowVariable) (dstIdx : Nat) : M Unit := do
    match arg with
    | .index src srcIdx => addEdge { var := src, idx := srcIdx } true { var := dst, idx := dstIdx }
    | .const name innerArgs => innerArgs.forM (handleInnerArg · dst dstIdx)
    | .func dom codom =>
      handleInnerArg dom dst dstIdx
      handleInnerArg codom dst dstIdx

  addEdge (src : Node) (growing : Bool) (dst : Node) : M Unit := do
    let edge := { node := dst, growing }
    let helper :=
      fun
        | none => some { edge }
        | some es => some (es.insert edge)
    modify fun s =>
      { s with
          nodes := s.nodes.insert src |>.insert dst,
          edges := s.edges.alter src helper }

end ConstraintGraph

public def constraintsSolvable (constraints : List FlowConstraint) (mono : MonoAnalysisState) :
    Bool := Id.run do
  let graph := ConstraintGraph.ofConstraints constraints mono
  let sccs := SCC.scc graph.nodes.toList fun node =>
    let edges := graph.edges.getD node {}
    edges.toList.map Edge.node
  let mut sccIndex := Std.HashMap.emptyWithCapacity graph.nodes.size
  let mut idx := 0
  for scc in sccs do
    for node in scc do
      sccIndex := sccIndex.insert node idx
    idx := idx + 1

  for (node, edges) in graph.edges do
    for edge in edges do
      if edge.growing then
        let scc1 := sccIndex[node]!
        let scc2 := sccIndex[edge.node]!
        if scc1 == scc2 then
          return false
  return true

structure SolveCtx where
  /--
  The (non-ground) rules that we need to apply until a fixpoint is reached.
  -/
  rules : Array FlowConstraint

abbrev FactIndex : Type := Std.HashMap FlowVariable (Std.HashSet GroundInput)

namespace FactIndex

def insert (factIndex : FactIndex) (fact : GroundConstraint) : FactIndex :=
  factIndex.alter fact.dst
    fun
      | some srcs => some <| srcs.insert fact.src
      | none => some { fact.src }

def contains (factIndex : FactIndex) (fact : GroundConstraint) : Bool :=
  factIndex[fact.dst]? |>.map (·.contains fact.src) |>.getD false

end FactIndex

structure SolveState where
  /--
  Whether the last iteration of the fixpoint solver caused a change.
  -/
  changed : Bool := false
  /--
  Ground facts that we have so far collected about the constraint system.
  Keys are destinations, the set in the value contains the sources.
  -/
  factIndex : FactIndex
  /--
  An accumulator for new facts in this iteration of the fixpoint solver.
  -/
  newFacts : List GroundConstraint := []

abbrev SolveM := ReaderT SolveCtx <| StateM SolveState


mutual

def partiallyInstantiateFlowType (arg : FlowTypeArg) (fact : GroundConstraint) : FlowTypeArg :=
  match arg with
  | .const name args => .const name (partiallyInstantiate args fact)
  | .index var idx =>
    if var == fact.dst then
      fact.src.args[idx]! |>.toFlowTypeArg
    else
      .index var idx
  | .func dom codom =>
    .func (partiallyInstantiateFlowType dom fact) (partiallyInstantiateFlowType codom fact)

def partiallyInstantiate (args : Array FlowTypeArg) (fact : GroundConstraint) : Array FlowTypeArg :=
  args.map (partiallyInstantiateFlowType · fact)

end

@[inline]
def learnFact (fact : GroundConstraint) : SolveM Unit := do
  modify fun s => { s with newFacts := fact :: s.newFacts }

@[inline]
def getSourcesFor (dst : FlowVariable) : SolveM (Std.HashSet GroundInput) := do
  return (← get).factIndex[dst]? |>.getD {}

partial def workRule (rule : FlowConstraint) : SolveM Unit := do
  match rule.src with
  | .vec args =>
    match FlowTypeArg.findTypeVarIn args with
    | some dst =>
      -- the rule is not ground, instantiate one argument and repeat until grounded
      for src in ← getSourcesFor dst do
        let newArgs := partiallyInstantiate args { src, dst }
        -- TODO: this could be simplified with FlowInput.ofTypes if we were in a monad with mono
        -- information
        let newRule := { rule with src := .vec newArgs }
        workRule newRule
    | none =>
      -- The rule is already ground
      learnFact { src := rule.src.toGroundInput.get! , dst := rule.dst  }
  | .var dst =>
    -- we have dst ⊑ rule.dst and find src ⊑ dst
    -- -> need to forward src into rule.dst
    for src in ← getSourcesFor dst do
      learnFact { src, dst := rule.dst }

def commitNewFacts : SolveM Unit := do
  for fact in (← get).newFacts do
    modify fun { factIndex, changed, newFacts } =>
      let contains := factIndex.contains fact
      let factIndex := factIndex.insert fact
      { factIndex, changed := changed || !contains, newFacts }
  modify fun s => { s with newFacts := [] }

def step : SolveM Unit := do
  for rule in (← read).rules do
    workRule rule
  commitNewFacts

partial def fixpoint : SolveM Unit := do
  modify fun s => { s with changed := false }
  step
  if (← get).changed then
    fixpoint
  else
    return ()

public partial def solveConstraints (constraints : List FlowConstraint) :
    Std.HashMap FlowVariable (List GroundInput) := Id.run do
  let mut facts := {}
  let mut rules := #[]
  for constraint in constraints do
    match constraint.src.toGroundInput with
    | some ground => facts := facts.insert ⟨ground, constraint.dst⟩
    | none => rules := rules.push constraint
  let (_, st) := fixpoint |>.run { rules } |>.run { factIndex := facts }
  let mut solution := {}
  for (dst, srcs) in st.factIndex do
    solution := solution.insert dst srcs.toList
  return solution

end Solve
end Monomorphization
end Transformation
end Chako
