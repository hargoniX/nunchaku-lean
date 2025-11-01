module

public import Chako.Util.Pipeline
public import Chako.Util.Model
import Chako.Util.Decode

/-!
This module contains the transformation for abstracting free variables that are types formers into
into axioms in order to enable specialisations of types that depend on free variables.
-/

namespace Chako
namespace Transformation
namespace AbstractTypes

open Lean

section Decode

open Decode

structure DecodeCtx where
  decodeTable : Std.HashMap String String

abbrev DecodeM := ReaderT DecodeCtx TransforM

def decodeUninterpretedTypeInhabitant (name : String) : DecodeM String := do
  let some endPos := name.revPosOf '_' | throwError m!"Weird type inhabitant name: {name}"
  let typeName := name.extract ⟨1⟩ endPos
  let typeId := name.extract endPos name.endPos
  let decodedTypeName := (← read).decodeTable[typeName]!
  return s!"${decodedTypeName}{typeId}"

def decodeConstName (name : String) : DecodeM String :=
  if name.startsWith "$" && !name.startsWith "$$" then
    decodeUninterpretedTypeInhabitant name
  else
    return (← read).decodeTable.getD name name

instance : MonadDecode DecodeM :=
    MonadDecode.Simple.instanceFactory
      decodeConstName
      decodeConstName
      decodeUninterpretedTypeInhabitant

def decode (model : NunModel) : DecodeM NunModel :=
  MonadDecode.decodeModel model

end Decode

public def transformation : Transformation Lean.MVarId Lean.MVarId NunResult NunResult where
  st := DecodeCtx
  inner := {
    name := "Abstract Types"
    encode g := g.withContext do
      let mut subst : Std.HashMap FVarId Expr := {}
      let mut decodeTable : Std.HashMap String String := {}
      for decl in ← getLCtx do
        if decl.isImplementationDetail then
          continue
        let fvar := decl.fvarId
        if (← fvar.getType) matches .sort (.succ ..) then
          trace[nunchaku.abstract] m!"Going to abstract {mkFVar fvar}"
          let name ← mkAuxDeclName (← fvar.getUserName)
          let axiomDecl := {
            name,
            levelParams := [],
            type := (← decl.fvarId.getType),
            isUnsafe := false
          }
          addDecl <| .axiomDecl axiomDecl
          subst := subst.insert decl.fvarId (mkConst name [])
          decodeTable := decodeTable.insert name.toString (← fvar.getUserName).toString

      let newLCtx := subst.fold (init := ← getLCtx) (fun lctx fvar ax => lctx.replaceFVarId fvar ax)
      let (fvars, vs) := subst.fold (init := (#[], #[]))
        fun (fvars, vs) fvar ax => (fvars.push (mkFVar fvar), vs.push ax)
      let newType := (← g.getType).replaceFVars fvars vs
      -- TODO: Possibly think about local instances
      Meta.withLCtx' newLCtx do
        let g := (← Meta.mkFreshExprMVar (some newType) .natural g.name).mvarId!
        trace[nunchaku.abstract] m!"Result: {g}"
        return (g, { decodeTable })
    decode ctx res :=
      ReaderT.run (res.mapM decode) ctx
  }

end AbstractTypes
end Transformation
end Chako
