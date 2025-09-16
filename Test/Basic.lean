module
import all Nunchaku

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


/--
info: The prover found a counter example
---
error: unsolved goals
n : Nat
⊢ let m := n + Nat.zero.succ;
  m = n
-/
#guard_msgs in
example (n : Nat) :
    let m := n + (.succ .zero)
    m = n := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
n : Nat
m : Nat := n + Nat.zero.succ
⊢ m = n
-/
#guard_msgs in
example (n : Nat) :
    let m := n + (.succ .zero)
    m = n := by
  intro m
  nunchaku

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
example (n m : Nat) (h1 : Even n) (h2 : Even m) : Odd (n.add m) := by
  nunchaku

mutual

inductive A where
  | base
  | step : B → A

inductive B where
  | base
  | step : A → B

end

/--
info: The prover is convinced that the theorem is true.
---
error: unsolved goals
x : A
⊢ A.step (B.step x) ≠ x
-/
#guard_msgs in
example (x : A) : (.step (.step x)) ≠ x := by nunchaku

mutual

def isEven (x : Nat) : Bool :=
  match x with
  | .zero => true
  | .succ n => isOdd n

def isOdd (n : Nat) : Bool :=
  match n with
  | .zero => false
  | .succ n => isEven n

end

/--
info: The prover found a counter example
---
error: unsolved goals
n : Nat
h : isEven n = true
⊢ isEven n.succ = true
-/
#guard_msgs in
example (n : Nat) (h : isEven n) : isEven n.succ := by
  nunchaku

mutual

def IsEven (x : Nat) : Prop :=
  match x with
  | .zero => True
  | .succ n => IsOdd n

def IsOdd (n : Nat) : Prop :=
  match n with
  | .zero => False
  | .succ n => IsEven n

end

/--
info: The prover found a counter example
---
error: unsolved goals
n : Nat
h : IsEven n
⊢ IsEven n.succ
-/
#guard_msgs in
example (n : Nat) (h : IsEven n) : IsEven n.succ := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
n : Nat
⊢ IsEven n ↔ isOdd n = true
-/
#guard_msgs in
example (n : Nat) : IsEven n ↔ isOdd n := by
  nunchaku

end Mutual

def isZero (n : Nat) : Bool :=
  match n with
  | 0 => true
  | _ + 1 => false

/--
info: The prover found a counter example
---
error: unsolved goals
n : Nat
⊢ isZero n = true
-/
#guard_msgs in
example (n : Nat) : isZero n := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
a b : Nat
⊢ a.ble b = true ↔ a.beq b = true
-/
#guard_msgs in
example (a b : Nat) : Nat.ble a b ↔ Nat.beq a b := by
  nunchaku


/--
info: The prover found a counter example
---
error: unsolved goals
a b : Nat
⊢ a.blt b = true ↔ a < b
-/
#guard_msgs in
example (a b : Nat) : Nat.blt a b ↔ a < b := by
  nunchaku


/--
info: The prover found a counter example
---
error: unsolved goals
n m k : Nat
⊢ n + m = n + k → m ≠ k
-/
#guard_msgs in
example {n m k : Nat} : n + m = n + k → m ≠ k := by
  nunchaku

/-
TODO: CVC4 currently straight up gives up on this. However if we specialised instances
(should lean or nunchaku do that?) it just works.


set_option trace.nunchaku true in
example {n m : Nat} : n < m → n ≤ m := by
  nunchaku
  -/

