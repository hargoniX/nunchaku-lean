module

namespace Chako

public section

/-
Constants used to encode ite without dealing with Decidable. This is sensible as nunchaku just
assumes decidability of everything anyway so there is no need to translate them.
-/

opaque classicalIf {α : Sort u} (d : Prop) (t e : α) : α := t

end

end Chako
