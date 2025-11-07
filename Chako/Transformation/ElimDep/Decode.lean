module
public import Chako.Transformation.ElimDep.Basic
public import Chako.Util.Decode

/-!
This module contains the decoding logic for the dependent type elimination.
-/

namespace Chako
namespace Transformation
namespace ElimDep

open Lean
open Decode

public abbrev DecodeM := ReaderT DecodeCtx TransforM

def decodeUninterpretedTypeInhabitant (name : String) : DecodeM String := do
  let some endPos := name.revPosOf '_' | throwError m!"Weird type inhabitant name: {name}"
  let typeName := name.extract ⟨1⟩ endPos
  let typeId := name.extract endPos name.endPos
  let decodedTypeName := (← read).decodeTable[typeName]!
  return s!"${decodedTypeName}{typeId}"

def decodeConstName (name : String) : DecodeM String := do
  if name.startsWith "$" && !name.startsWith "$$" then
    decodeUninterpretedTypeInhabitant name
  else
    match (← read).decodeTable[name]? with
    | some name =>
      let unitSet := (← read).unitSet
      if unitSet.contains name then
        return "PUnit"
      else if unitSet.contains (name.dropRight (auxiliaryUnitCtor.toString.length + 1)) then
        return "PUnit.punit"
      else
        return name
    | none => return name

instance : MonadDecode DecodeM :=
    MonadDecode.Simple.instanceFactory
      decodeConstName
      decodeConstName
      decodeUninterpretedTypeInhabitant

public def decode (model : NunModel) : DecodeM NunModel :=
  MonadDecode.decodeModel model

end ElimDep
end Transformation
end Chako
