module
import all Nunchaku


structure Foo where
  x : Nat
  y : Nat
  h : x = y

/--
info: The prover is convinced that the theorem is true.
---
error: unsolved goals
f : Foo
⊢ f.x = f.y
-/
#guard_msgs in
example (f : Foo) : f.x = f.y := by
  nunchaku

/--
info: The prover is convinced that the theorem is true.
---
error: unsolved goals
producer : Nat → Foo
⊢ (producer Nat.zero).x = (producer Nat.zero).y
-/
#guard_msgs in
example (producer : Nat → Foo) : (producer .zero).x = (producer .zero).y := by
  nunchaku

-- TODO: something with type params
