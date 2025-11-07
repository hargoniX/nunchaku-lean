module

namespace Chako

public section

/-!
This module contains auxiliary constants used in the translation steps.
-/

open Classical in
/--
The actual `ite` declaration requires `Decidable p` but Nunchaku is a classical system so we can
just work with the discriminant and both branches.
-/
noncomputable opaque classicalIf {α : Sort u} (d : Prop) (t e : α) : α := if d then t else e

end

end Chako
