module

public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.Model

/-!
This module contains the transformation for negating the goal should that be necessary.
-/

namespace Nunchaku
namespace Transformation
namespace Falsify

public def transformation : Transformation Lean.MVarId Lean.MVarId LeanResult LeanResult where
  st := private Unit
  inner := private {
    name := "Falsify"
    encode g := g.withContext do
      if (← read).falsify then
        let g := (← Lean.Meta.mkFreshExprMVar (Lean.mkNot (← g.getType))).mvarId!
        trace[nunchaku.falsify] m!"Result: {g}"
        return (g, ())
      else
        trace[nunchaku.falsify] m!"Result: {g}"
        return (g, ())
    decode _ res := return res
  }

end Falsify
end Transformation
end Nunchaku
