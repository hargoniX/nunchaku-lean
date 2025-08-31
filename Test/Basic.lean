import Nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
n m : Nat
h : n = m
⊢ n ≠ m
-/
#guard_msgs in
example (n m : Nat) (h : n = m) : n ≠ m := by nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
n m : Nat
⊢ n.add n = n.add m
-/
#guard_msgs in
example (n m : Nat) : n.add n = n.add m := by nunchaku

/--
info: The prover wasn't able to prove or disprove the theorem.
---
error: unsolved goals
n m : Nat
⊢ n.add m = m.add n
-/
#guard_msgs in
example (n m : Nat) : n.add m = m.add n := by nunchaku (timeout := 1)


inductive MyEven : Nat → Prop where
  | zero : MyEven Nat.zero
  | succ : MyEven n → MyEven n.succ.succ

/--
info: The prover found a counter example
---
error: unsolved goals
n : Nat
⊢ MyEven n
-/
#guard_msgs in
example (n : Nat) : MyEven n := by nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
n : Nat
h : MyEven n
⊢ MyEven n.succ
-/
#guard_msgs in
example (n : Nat) (h : MyEven n) : MyEven n.succ := by nunchaku

/--
info: The prover is convinced that the theorem is true.
---
error: unsolved goals
n : Nat
⊢ n ≠ n.succ
-/
#guard_msgs in
example (n : Nat) : n ≠ n.succ := by nunchaku

namespace Mutual

mutual

inductive Even : Nat → Prop where
  | zero : Even Nat.zero
  | step : Odd n → Even n.succ

inductive Odd : Nat → Prop where
  | step : Even n → Odd n.succ

end

/--
info: The prover found a counter example
---
error: unsolved goals
n m : Nat
h1 : Even n
h2 : Even m
⊢ Odd (n.add m)
-/
#guard_msgs in
example (n m : Nat) (h1 : Even n) (h2 : Even m) : Odd (n.add m) := by nunchaku

mutual

inductive A where
  | base
  | step : B → A

inductive B where
  | step : A → B

end

set_option trace.nunchaku.output true in
example (x : A) : (.step (.step x)) ≠ x := by nunchaku

end Mutual
