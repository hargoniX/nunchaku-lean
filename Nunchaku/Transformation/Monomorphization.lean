module

public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.Model
import Nunchaku.Util.AddDecls
import Nunchaku.Util.NunchakuBuilder
import Nunchaku.Util.NunchakuPrinter

import Nunchaku.Transformation.Monomorphization.Collect
import Nunchaku.Transformation.Monomorphization.Solve
import Nunchaku.Transformation.Monomorphization.Specialise

/-!
This module contains the monomorphisation transformation, it is based on
["The Simple Essence of Monomorphization"](https://se.cs.uni-tuebingen.de/publications/lutze25simple.pdf)
though restricted to the simplest possible fragment in Lean for now.
-/

namespace Nunchaku
namespace Transformation
namespace Monomorphization

open Lean

open Collect Solve Specialise

-- TODO: Dedup this framework with output as far as possible
abbrev DecodeM := ReaderT DecodeCtx TransforM

def decodeConstName (name : String) : DecodeM String :=
  return (← read).decodeTable[name]? |>.map Prod.fst |>.getD name

def GroundTypeArg.toNunType : GroundTypeArg → NunType
  | .const name args => .const name.toString (args.map GroundTypeArg.toNunType).toList
  | .func dom codom => .arrow dom.toNunType codom.toNunType

def GroundInput.toNunType (inp : GroundInput) : List NunType :=
  inp.args.map GroundTypeArg.toNunType |>.toList

def decodeType (t : NunType) : DecodeM NunType := do
  match t with
  | .prop | .type => return t
  | .const name [] =>
    let decodedName ← decodeConstName name
    match (← read).decodeTable[name]? with
    | some (_, input) => return .const decodedName input.toNunType
    | none => return .const decodedName []
  | .const _ _ => throwError m!"Expected only monomorphic types in decoding: {t}"
  | .arrow l r => return .arrow (← decodeType l) (← decodeType r)

def decodeTerm (t : NunTerm) : DecodeM NunTerm := do
  match t with
  | .var .. | .builtin .. => return t
  | .const name => return .const (← decodeConstName name)
  | .lam id ty body => return .lam id (← decodeType ty) (← decodeTerm body)
  | .forall id ty body => return .forall id (← decodeType ty) (← decodeTerm body)
  | .exists id ty body => return .exists id (← decodeType ty) (← decodeTerm body)
  | .let id value body => return .let id (← decodeTerm value) (← decodeTerm body)
  | .app fn arg => return .app (← decodeTerm fn) (← decodeTerm arg)

def decode (model : NunModel) : DecodeM NunModel := do
  let decls : List NunModelDecl ← model.decls.mapM fun decl => do
    match decl with
    | .type name members =>
      -- We don't touch uninterpreted types in this pipeline step
      return .type name members
    | .val name value =>
      match (← read).decodeTable[name]? with
      | some (decoded, args) =>
        if !args.args.isEmpty then
          throwError "Found uninterpreted symbol with type arguments in model: {name}"
        return .val decoded (← decodeTerm value)
      | none =>
        return .val name (← decodeTerm value)
  return { decls }

public def transformation : Transformation MVarId MVarId NunResult NunResult where
  st := DecodeCtx
  inner := {
    name := "Monomorphisation"
    encode g := g.withContext do
      let (constraints, monoAnalysis) ← (collectConstraints g).run
      if h : !constraintsSolvable constraints then
        throwError "The goal cannot be monomorphised."
      else
        trace[nunchaku.mono] m!"Constraints: {constraints}"
        let solution := solveConstraints constraints (by simpa using h)
        trace[nunchaku.mono] m!"Solution: {solution.toList}"
        let (g, d) ← (specialize g).run { solution } monoAnalysis
        trace[nunchaku.mono] m!"Result: {g}"
        return (g, d)
    decode ctx res :=
      ReaderT.run (res.mapM decode) ctx
  }

end Monomorphization
end Transformation
end Nunchaku
