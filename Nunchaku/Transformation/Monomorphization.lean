module

public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.Model
import Nunchaku.Util.AddDecls
import Nunchaku.Util.Decode
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

section Decode

open Decode

abbrev DecodeM := ReaderT DecodeCtx TransforM

def decodeUninterpretedTypeInhabitant (name : String) : DecodeM String := do
  let some endPos := name.revPosOf '_' | throwError m!"Weird type inhabitant name: {name}"
  let typeName := name.extract ⟨1⟩ endPos
  let typeId := name.extract endPos name.endPos
  if !(← read).decodeTable.contains typeName then
    throwError "Ahhh"
  let decodedTypeName := (← read).decodeTable[typeName]!.fst
  return s!"${decodedTypeName}{typeId}"

def decodeConstName (name : String) : DecodeM String :=
  if name.startsWith "$" && !name.startsWith "$$" then
    decodeUninterpretedTypeInhabitant name
  else
    return (← read).decodeTable[name]?.map Prod.fst |>.getD name

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

instance : MonadDecode DecodeM where
  decodeConstName := decodeConstName
  decodeUninterpretedTypeName := decodeConstName
  decodeUninterpretedTypeInhabitant := decodeUninterpretedTypeInhabitant
  decodeType := decodeType

def decode (model : NunModel) : DecodeM NunModel := do
  MonadDecode.decodeModel model

end Decode

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
