module
public meta import Lean.Elab.Command
import Lean.Elab.Command
meta import Chako.Frontend
meta import Chako.Transformation

namespace Chako
namespace Eval

public section

open Lean

inductive ResultKind where
  | counterExample
  | proven
  | gaveUp
  | recoveryError (e : Exception)
  | nunchakuError (e : Exception)
  | encodingError (e : Exception)

structure Duration where
  encodingMs : Nat
  nunchakuMs : Nat
  recoveryMs : Nat

def Duration.toMessageData (dur : Duration) : MessageData :=
  m!"encoding: {dur.encodingMs}ms, nunchaku: {dur.nunchakuMs}ms, recovery: {dur.recoveryMs}ms"

instance : ToMessageData Duration where
  toMessageData := Duration.toMessageData

structure Result where
  thm : Name
  mutation : Option Nat
  kind : ResultKind
  duration : Duration

def Result.toMessageData (res : Result) : MessageData :=
  match res.kind with
  | .counterExample => m!"{res.thm} counter example found with time: {res.duration}"
  | .proven => m!"{res.thm} proved with time: {res.duration}"
  | .gaveUp => m!"{res.thm} given up on after time: {res.duration}"
  | .recoveryError err =>
    m!"{res.thm} recovery error after time: {res.duration}\n{err.toMessageData}"
  | .nunchakuError err =>
    m!"{res.thm} nunchaku error after time: {res.duration}\n{err.toMessageData}"
  | .encodingError err =>
    m!"{res.thm} encoding error after time: {res.duration}\n{err.toMessageData}"

instance : ToMessageData Result where
  toMessageData := Result.toMessageData

structure Problem where
  thm : Name
  info : TheoremVal
  mutation : Option Nat
  g : MVarId
  deriving Inhabited

structure Timed (α : Type u) where
  x : α
  timeMs : Nat

meta def Problem.fromTheorem (info : TheoremVal) : MetaM (Array Problem) := do
  let mvar := (← Meta.mkFreshExprMVar info.type).mvarId!
  return #[{
    thm := info.name,
    info := info,
    mutation := none,
    g := mvar
  }]

meta def Problem.mutationsFromTheorem (info : TheoremVal) : MetaM (Array Problem) := do
  let mutantCandidates ← go #[] info.type #[]
  let mut problems := Array.emptyWithCapacity mutantCandidates.size
  for h : idx in 0...mutantCandidates.size do
    let mutant := mutantCandidates[idx]
    let mvar := (← Meta.mkFreshExprMVar mutant).mvarId!
    problems := problems.push {
      thm := info.name,
      info := info,
      mutation := (some idx),
      g := mvar,
    }
  return problems
where
  go (args : Array Expr) (remainder : Expr) (mutants : Array Expr) : MetaM (Array Expr) := do
    if remainder.isForall then
      Meta.forallBoundedTelescope remainder (some 1) fun newArg remainder => do
        let newArg := newArg[0]!
        /-
        If it is not a proof we don't want to scramble it. If it is a proof and occurs in the
        remainder of the theorem we also don't want to scramble it for type correctness issues.
        -/
        if remainder.containsFVar newArg.fvarId! || !(← Meta.isProof newArg) then
          go (args.push newArg) remainder mutants
        else
          -- Simple mutant where we drop the assumption
          let mutant ← Meta.mkForallFVars args remainder
          let mutants := mutants.push mutant
          go (args.push newArg) remainder mutants
    else
      -- Simple mutant where we invert the conclusion
      let mutant := ← Meta.mkForallFVars args (mkNot remainder)
      let mutants := mutants.push mutant
      return mutants

meta def timedRun [Monad m] [MonadExceptOf Exception m] [MonadLiftT BaseIO m] (x : m α) : m (Timed (Except Exception α)) := do
  let startTime ← IO.monoMsNow
  try
    let res ← x
    let endTime ← IO.monoMsNow
    return ⟨.ok res, endTime - startTime⟩
  catch ex =>
    let endTime ← IO.monoMsNow
    return ⟨.error ex, endTime - startTime⟩

meta def tryChakoOn (evalProblem : Problem) : MetaM Result := do
  let g := evalProblem.g
  let (_, g) ← g.intros

  TransforM.run g { timeout := 2 } do
    withoutModifyingEnv do
      let { timeMs := encodingMs, x := res } ← timedRun (Transformation.pipeline.run g)
      match res with
      | .ok (problem, back) =>
        let { timeMs := nunchakuMs, x := res} ← timedRun (runSolver problem (← TransforM.getConfig))
        match res with
        | .ok res =>
          let { timeMs := recoveryMs, x := res} ← timedRun (back res)
          match res with
          | .ok res =>
            let kind :=
              match res with
              | .unsat => .proven
              | .unknown => .gaveUp
              | .sat .. => .counterExample
            return {
              thm := evalProblem.thm,
              mutation := evalProblem.mutation,
              kind,
              duration := {
                encodingMs,
                nunchakuMs,
                recoveryMs,
              }
            }
          | .error ex =>
            return {
              thm := evalProblem.thm,
              mutation := evalProblem.mutation,
              kind := .recoveryError ex,
              duration := {
                encodingMs,
                nunchakuMs,
                recoveryMs,
              }
            }
        | .error ex =>
          return {
            thm := evalProblem.thm,
            mutation := evalProblem.mutation,
            kind := .nunchakuError ex,
            duration := {
              encodingMs,
              nunchakuMs,
              recoveryMs := 0,
            }
          }
      | .error ex =>
        return {
          thm := evalProblem.thm,
          mutation := evalProblem.mutation,
          kind := .encodingError ex,
          duration := {
            encodingMs,
            nunchakuMs := 0,
            recoveryMs := 0,
          }
        }


meta def isBlackListed (declName : Name) : CoreM Bool := do
  match ← findDeclarationRanges? declName with
  | some _ =>
    let env ← getEnv
    pure (declName.isInternal)
    <||> (pure <| isAuxRecursor env declName)
    <||> (pure <| isNoConfusion env declName)
    <||> (pure <| declName.isInternalDetail)
    <||> isRec declName
    <||> Meta.isMatcher declName
  | none => return true

meta def evalChako (targetModule : Name) (file : System.FilePath)
    (problemGenerator : TheoremVal → MetaM (Array Problem)) : MetaM Unit := do
  let env ← getEnv
  let some targetModuleIdx := env.getModuleIdx? targetModule |
    throwError m!"Not a module: {targetModule}"
  let mut targets := #[]
  for (name, cinfo) in env.constants do
    if (← isBlackListed name) then
      continue
    let some modidx := env.getModuleIdxFor? name |
      throwError m!"Found no module for {name}"
    if modidx == targetModuleIdx then
      if let .thmInfo cinfo := cinfo then
        targets := targets ++ (← problemGenerator cinfo)
  let out ← IO.FS.Handle.mk file .write
  out.putStrLn "theorem,mutant,result,encoding,nunchaku,recovery"
  targets.forM fun target => do
    let res ← tryChakoOn target
    let mut resStr := s!"{target.thm},"
    resStr := resStr ++ s!"{target.mutation.getD 0},"
    resStr :=
      resStr ++
        match res.kind with
        | .counterExample => "SAT,"
        | .proven => "UNSAT,"
        | .gaveUp => "UNKNOWN,"
        | .recoveryError .. => "ERR_RECOVERY,"
        | .nunchakuError .. => "ERR_NUNCHAKU,"
        | .encodingError .. => "ERR_ENCODING,"
    resStr := resStr ++ s!"{res.duration.encodingMs},"
    resStr := resStr ++ s!"{res.duration.nunchakuMs},"
    resStr := resStr ++ s!"{res.duration.recoveryMs}"
    out.putStrLn resStr

elab "#eval_chako_sound_module" id:ident file:str : command => do
  Elab.Command.liftTermElabM (evalChako id.getId file.getString Problem.fromTheorem)

elab "#eval_chako_perf_module" id:ident file:str : command => do
  Elab.Command.liftTermElabM (evalChako id.getId file.getString Problem.mutationsFromTheorem)

elab "#eval_chako_sound_decl" id:ident : command => do
  Elab.Command.liftTermElabM do
    let .thmInfo cinfo ← getConstInfo id.getId
      | throwError m!"Not a theorem {id}"
    let problem ← Problem.fromTheorem cinfo
    let res ← tryChakoOn problem[0]!
    logInfo m!"{res}"

elab "#eval_chako_perf_decl" id:ident : command => do
  Elab.Command.liftTermElabM do
    let .thmInfo cinfo ← getConstInfo id.getId
      | throwError m!"Not a theorem {id}"
    let problems ← Problem.mutationsFromTheorem cinfo
    for problem in problems do
      logInfo m!"{problem.g}"
      let res ← tryChakoOn problem
      logInfo m!"{res}"

end

end Eval
end Chako
