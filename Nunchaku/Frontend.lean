import Lean
import Nunchaku.Attr
import Nunchaku.Transformation
import Nunchaku.Util.Model
import Nunchaku.Util.NunchakuPrinter

/-!
This module contains the main entry point to the nunchaku tactic.
-/

namespace Nunchaku

open Lean Elab Tactic

private def runSolver (problem : NunProblem) (cfg : NunchakuConfig) :
    MetaM NunResult := do
  IO.FS.withTempFile fun nunHandle nunPath => do
    withTraceNode `nunchaku.solver (fun _ => return "Serializing Nunchaku Problem") do
      let problem ← IO.lazyPure fun _ => toString problem
      trace[nunchaku.output] s!"Handing problem to solver:\n{problem}"
      nunHandle.putStr problem
      nunHandle.flush

    -- TODO: configurable solver path
    let cmd := "nunchaku"
    let mut args := #[
      "--checks",
      -- TODO: proper solver params
      "-s",
      "cvc4",
      "-i",
      "nunchaku",
      "-nc",
      "--timeout",
      s!"{cfg.timeout}",
      nunPath.toString
    ]

    let out? ← BVDecide.External.runInterruptible (cfg.timeout + 1) { cmd, args, stdin := .piped, stdout := .piped, stderr := .null }
    match out? with
    | .timeout =>
      let mut err := "Nunchaku timed out while solving the problem.\n"
      err := err ++ "Consider increasing the timeout with the `timeout` config option.\n"
      throwError err
    | .success { exitCode := exitCode, stdout := stdout, stderr := stderr} =>
      if exitCode == 255 then
        throwError s!"Failed to execute external prover:\n{stderr}"
      else
        if stdout.startsWith "UNSAT" then
          return .unsat
        else if stdout.startsWith "SAT" then
          -- TODO: model parsing
          return .sat ()
        else if stdout.startsWith "UNKNOWN" then
          return .unknown
        else
          throwError s!"The external prover produced unexpected output, stdout:\n{stdout}stderr:\n{stderr}"

def runNunchaku (g : MVarId) (cfg : NunchakuConfig) : MetaM LeanResult := do
  TransforM.run g cfg do
    let (problem, back) ←
      withTraceNode `nunchaku (fun _ => return "Running forward pipeline") do
        Transformation.pipeline.run g
    let res ←
      withTraceNode `nunchaku (fun _ => return "Running the solver") do
        runSolver problem (← TransforM.getConfig)
    withTraceNode `nunchaku (fun _ => return "Running the backwards pipeline") do
      back res

@[tactic nunchakuStx]
def evalNunchaku : Tactic
  | `(tactic| nunchaku $cfg:optConfig) => do
    let cfg ← elabNunchakuConfig cfg
    let res ← runNunchaku (← getMainGoal) cfg
    logInfo m!"{res}"
  | _ => throwUnsupportedSyntax

end Nunchaku
