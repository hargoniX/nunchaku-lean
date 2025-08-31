import Nunchaku.Util.Pipeline
import Nunchaku.Util.Model

/-!
This module contains the transformation for negating the goal should that be necessary.
-/

namespace Nunchaku
namespace Transformation
namespace Falsify

def transformation : Transformation Lean.MVarId Lean.MVarId LeanResult LeanResult where
  st := Unit
  inner := {
    name := "Falsify"
    encode g := g.withContext do
      if (← read).falsify then
        let g ← Lean.Meta.mkFreshExprMVar (Lean.mkNot (← g.getType))
        return (g.mvarId!, ())
      else
        return (g, ())
    decode _ res := return res
  }

end Falsify
end Transformation
end Nunchaku
