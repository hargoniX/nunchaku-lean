# Chako
Chako is a counter example finder for a fragment of Lean 4, backed by the finite model finder
Nunchaku.

```lean
import Chako

/--
info: Chako found a counter example:
inductive α where | $α_0
val f := (fun (v_0 : α) . $α_0)
val xs := List.nil
---
error: unsolved goals
α : Type
xs : List α
f : α → α
⊢ List.map f xs ≠ xs
-/
#guard_msgs in
example (α : Type) (xs : List α) (f : α → α) : xs.map f ≠ xs := by
  chako
```

The name Chako is the coloquial version of Tabak-Tayok, a Filipino nunchaku-style weapon.
