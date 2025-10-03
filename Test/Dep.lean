import Nunchaku


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

/--
info: The prover wasn't able to prove or disprove the theorem.
---
error: unsolved goals
xs : List Foo
⊢ ∀ (x : Foo), x ∈ xs → x.x = x.y
-/
#guard_msgs in
example (xs : List Foo) : ∀ x ∈ xs, x.x = x.y := by
  nunchaku
