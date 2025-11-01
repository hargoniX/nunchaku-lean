module
import Chako.Util.NunchakuBuilder
import Chako.Util.NunchakuPrinter
public import Chako.Util.Model


namespace Chako
namespace Decode

public class MonadDecode (m : Type → Type) where
  decodeConstName : String → m String
  decodeUninterpretedTypeName : String → m String
  decodeUninterpretedTypeInhabitant : String → m String
  decodeType : NunType → m NunType

namespace MonadDecode

namespace Simple

@[specialize]
partial def decodeType [Monad m] (decodeConstName : String → m String)
    (t : NunType) : m NunType := do
  match t with
  | .prop | .type => return t
  | .const name args =>
    let decodedName ← decodeConstName name
    let decodedArgs ← args.mapM (decodeType decodeConstName)
    return .const decodedName decodedArgs
  | .arrow l r => return .arrow (← decodeType decodeConstName l) (← decodeType decodeConstName r)

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
