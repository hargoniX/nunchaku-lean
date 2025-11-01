module

public import Lean.Meta.Basic
public import Chako.Attr
public meta import Chako.Util.Model
import Chako.Transformation
meta import Chako.Transformation
meta import Chako.Util.ChakoPrinter
meta import Lean.Elab.Tactic.BVDecide.External
meta import Lean.Meta.Tactic.Intro

/-!
This module contains the main entry point to the nunchaku tactic.
-/

namespace Chako

open Lean Elab Tactic

public meta def runSolver (problem : NunProblem) (cfg : ChakoConfig) :
    MetaM NunResult := do
  IO.FS.withTempFile fun nunHandle nunPath => do
    withTraceNode `nunchaku.solver (fun _ => return "Serializing Chako problem") do
      let problem ← IO.lazyPure fun _ => toString problem
      trace[nunchaku.output] s!"Handing problem to Chako:\n{problem}"
      nunHandle.putStr problem
      nunHandle.flush

    if cfg.solvers.isEmpty then
      throwError m!"No solvers configured"
    let solvers := cfg.solvers.map (·.toCliArg) |>.toList |> String.intercalate ","
    -- TODO: configurable solver path
    let cmd := "nunchaku"
    let mut args := #[
      "--checks",
      "-s",
      solvers,
      "-i",
      "nunchaku",
      "-o",
      "sexp",
      "-nc",
      "--timeout",
      s!"{cfg.timeout}",
      nunPath.toString
    ]
    let strArgs := String.intercalate " " args.toList
    trace[nunchaku] m!"Calling solver with {strArgs}"

    let out? ← BVDecide.External.runInterruptible (cfg.timeout + 2) { cmd, args, stdin := .piped, stdout := .piped, stderr := .null }
    match out? with
    | .timeout =>
      let mut err := "Chako timed out while solving the problem.\n"
      err := err ++ "Consider increasing the timeout with the `timeout` config option.\n"
      throwError err
    | .success { exitCode := exitCode, stdout := stdout, stderr := stderr} =>
      if exitCode == 255 then
        throwError s!"Failed to execute Chako:\n{stderr}"
      else
        match NunResult.parse stdout with
        | .ok res => return res
        | .error err =>
          throwError s!"The external prover produced unexpected output:\n  {err}\nstdout:\n{stdout}stderr:\n{stderr}"

public meta def runChako (g : MVarId) (cfg : ChakoConfig) : MetaM NunResult := do
  TransforM.run g cfg do
    withoutModifyingEnv do
      let (problem, back) ←
        withTraceNode `nunchaku (fun _ => return "Running forward pipeline") do
          Transformation.pipeline.run g
      let res ←
        withTraceNode `nunchaku (fun _ => return "Running Chako") do
          runSolver problem (← TransforM.getConfig)
      withTraceNode `nunchaku (fun _ => return "Running the backwards pipeline") do
        back res

@[tactic nunchakuStx]
public meta def evalChako : Tactic
  | `(tactic| nunchaku $cfg:optConfig) => do
    let cfg ← elabChakoConfig cfg
    let res ← runChako (← getMainGoal) cfg
    logInfo m!"{res}"
  | _ => throwUnsupportedSyntax

end Chako
