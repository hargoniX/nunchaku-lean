module
import Chako.Util.NunchakuBuilder
import Chako.Util.NunchakuPrinter
public import Chako.Util.Model

/-!
This module contains infrastructure for the decoding part of pipeline steps. The key entrypoint
is `MonadDecode` together with `decodeModel`.
-/

namespace Chako
namespace Decode

/--
A marker type class for monads that allow for decoding of a model from after a pipeline step to
before the pipeline step. Usually this monad is going to carry around some form of inverse name
mapping.
-/
public class MonadDecode (m : Type → Type) where
  /--
  How to decode names of constants.
  -/
  decodeConstName : String → m String
  /--
  How to decode names of uninterpreted types (type parameters to the theorem).
  -/
  decodeUninterpretedTypeName : String → m String
  /--
  How to decode names of inhabitants of uninterpreted types.
  -/
  decodeUninterpretedTypeInhabitant : String → m String
  /--
  How to decode types in general. This one can often be filled in automatically by
  `instanceFactory`.
  -/
  decodeType : NunType → m NunType

namespace MonadDecode

namespace Simple

@[specialize]
partial def decodeType [Monad m] (decodeConstName : String → m String) (t : NunType) :
    m NunType := do
  match t with
  | .prop | .type => return t
  | .const name args =>
    let decodedName ← decodeConstName name
    let decodedArgs ← args.mapM (decodeType decodeConstName)
    return .const decodedName decodedArgs
  | .arrow l r => return .arrow (← decodeType decodeConstName l) (← decodeType decodeConstName r)

/--
Create a `MonadDecode` instance with a default `decodeType` mechanism that just decodes type names
recursively. This is often (but not always) a good solution for a decoding step.
-/
@[inline]
public def instanceFactory [Monad m] (decodeConstName : String → m String)
    (decodeUninterpretedTypeName : String → m String)
    (decodeUninterpretedTypeInhabitant : String → m String) : MonadDecode m where
  decodeConstName := decodeConstName
  decodeUninterpretedTypeName := decodeUninterpretedTypeName
  decodeUninterpretedTypeInhabitant := decodeUninterpretedTypeInhabitant
  decodeType := decodeType decodeConstName

end Simple

variable [Monad m] [MonadDecode m]

def decodeTerm (t : NunTerm) : m NunTerm := do
  match t with
  | .var .. | .builtin .. => return t
  | .const name => return .const (← decodeConstName name)
  | .lam binders body =>
    let binders ← binders.mapM fun (id, ty) => do return (id, ← decodeType ty)
    return .lam binders (← decodeTerm body)
  | .forall id ty body => return .forall id (← decodeType ty) (← decodeTerm body)
  | .exists id ty body => return .exists id (← decodeType ty) (← decodeTerm body)
  | .let id value body => return .let id (← decodeTerm value) (← decodeTerm body)
  | .app fn arg => return .app (← decodeTerm fn) (← decodeTerm arg)

/--
Decode a `NunModel` within some `m` that implements `MonadDecode`.
-/
public def decodeModel (model : NunModel) : m NunModel := do
  let decls : List NunModelDecl ← model.decls.mapM fun decl => do
    match decl with
    | .type name members =>
      let decodedName ← decodeUninterpretedTypeName name
      let decodedMembers ← members.mapM decodeUninterpretedTypeInhabitant
      return .type decodedName decodedMembers
    | .val name value =>
      let decodedName ← decodeConstName name
      let decodedValue ← decodeTerm value
      return .val decodedName decodedValue
    | .witness name value =>
      return .witness name (← decodeTerm value)
  return { decls }

end MonadDecode

end Decode
end Chako
