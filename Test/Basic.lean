import Chako

/--
info: Chako found a counter example:
val x := (Nat.succ Nat.zero)
val y := Nat.zero
---
error: unsolved goals
x y : Nat
⊢ (if (x == y) = true then panicWithPosWithDecl "Test.Basic" "_example" 13 38 "Ahh" else default + 1) = 0
-/
#guard_msgs in
example (x y : Nat) : (if x == y then panic! "Ahh" else default + 1) = 0 := by
  chako

/--
info: Chako found a counter example:
val m := Nat.zero
val n := Nat.zero
---
error: unsolved goals
n m : Nat
h : n = m
⊢ n ≠ m
-/
#guard_msgs in
example (n m : Nat) (h : n = m) : n ≠ m := by chako

/--
info: Chako found a counter example:
val m := Nat.zero
val n := (Nat.succ Nat.zero)
---
error: unsolved goals
n m : Nat
⊢ n.add n = n.add m
-/
#guard_msgs in
example (n m : Nat) : n.add n = n.add m := by chako

/--
info: Chako wasn't able to prove or disprove the theorem.
---
error: unsolved goals
n m : Nat
⊢ n.add m = m.add n
-/
#guard_msgs in
example (n m : Nat) : n.add m = m.add n := by chako (timeout := 1)


inductive MyEven : Nat → Prop where
  | zero : MyEven Nat.zero
  | succ : MyEven n → MyEven n.succ.succ

/--
info: Chako found a counter example:
val n := (Nat.succ Nat.zero)
---
error: unsolved goals
n : Nat
⊢ MyEven n
-/
#guard_msgs in
example (n : Nat) : MyEven n := by chako

/--
info: Chako found a counter example:
val n := Nat.zero
---
error: unsolved goals
n : Nat
h : MyEven n
⊢ MyEven n.succ
-/
#guard_msgs in
example (n : Nat) (h : MyEven n) : MyEven n.succ := by chako

/--
info: Chako is convinced that the theorem is true.
---
error: unsolved goals
n : Nat
⊢ n ≠ n.succ
-/
#guard_msgs in
example (n : Nat) : n ≠ n.succ := by chako


/--
info: Chako found a counter example:
val n := Nat.zero
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
  chako

/--
info: Chako found a counter example:
val m := Nat.zero
val n := Nat.zero
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
  chako

namespace Mutual

mutual

inductive Even : Nat → Prop where
  | zero : Even Nat.zero
  | step : Odd n → Even n.succ

inductive Odd : Nat → Prop where
  | step : Even n → Odd n.succ

end

/--
info: Chako found a counter example:
val m := Nat.zero
val n := Nat.zero
---
error: unsolved goals
n m : Nat
h1 : Even n
h2 : Even m
⊢ Odd (n.add m)
-/
#guard_msgs in
example (n m : Nat) (h1 : Even n) (h2 : Even m) : Odd (n.add m) := by
  chako

mutual

inductive A where
  | base
  | step : B → A

inductive B where
  | base
  | step : A → B

end

/--
info: Chako is convinced that the theorem is true.
---
error: unsolved goals
x : A
⊢ A.step (B.step x) ≠ x
-/
#guard_msgs in
example (x : A) : (.step (.step x)) ≠ x := by chako

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
info: Chako found a counter example:
val n := Nat.zero
---
error: unsolved goals
n : Nat
h : isEven n = true
⊢ isEven n.succ = true
-/
#guard_msgs in
example (n : Nat) (h : isEven n) : isEven n.succ := by
  chako

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
info: Chako found a counter example:
val n := Nat.zero
---
error: unsolved goals
n : Nat
h : IsEven n
⊢ IsEven n.succ
-/
#guard_msgs in
example (n : Nat) (h : IsEven n) : IsEven n.succ := by
  chako

/--
info: Chako found a counter example:
val n := Nat.zero
---
error: unsolved goals
n : Nat
⊢ IsEven n ↔ isOdd n = true
-/
#guard_msgs in
example (n : Nat) : IsEven n ↔ isOdd n := by
  chako

end Mutual

def isZero (n : Nat) : Bool :=
  match n with
  | 0 => true
  | _ + 1 => false

/--
info: Chako found a counter example:
val n := (Nat.succ Nat.zero)
---
error: unsolved goals
n : Nat
⊢ isZero n = true
-/
#guard_msgs in
example (n : Nat) : isZero n := by
  chako

/--
info: Chako found a counter example:
val a := Nat.zero
val b := (Nat.succ Nat.zero)
---
error: unsolved goals
a b : Nat
⊢ a.ble b = true ↔ a.beq b = true
-/
#guard_msgs in
example (a b : Nat) : Nat.ble a b ↔ Nat.beq a b := by
  chako


/--
info: Chako wasn't able to prove or disprove the theorem.
---
error: unsolved goals
a b : Nat
⊢ a.blt b = true ↔ a < b
-/
#guard_msgs in
example (a b : Nat) : Nat.blt a b ↔ a < b := by
  chako


/--
info: Chako found a counter example:
val k := Nat.zero
val m := Nat.zero
val n := Nat.zero
---
error: unsolved goals
n m k : Nat
⊢ n + m = n + k → m ≠ k
-/
#guard_msgs in
example {n m k : Nat} : n + m = n + k → m ≠ k := by
  chako

/--
info: Chako found a counter example:
val m := Nat.zero
val n := Nat.zero
---
error: unsolved goals
n m : Nat
⊢ n ≤ m → n < m
-/
#guard_msgs in
example {n m : Nat} : n ≤ m → n < m := by
  chako

/--
info: Chako is convinced that the theorem is true.
---
error: unsolved goals
a b : Unit
⊢ a = b
-/
#guard_msgs in
example (a b : Unit) : a = b := by
  chako

/--
info: Chako found a counter example:
val a := PUnit.punit
val b := PUnit.punit
---
error: unsolved goals
a b : Unit
⊢ a ≠ b
-/
#guard_msgs in
example (a b : Unit) : a ≠ b := by
  chako

/--
info: Chako is convinced that the theorem is true.
---
error: unsolved goals
a b : Unit
⊢ a = ()
-/
#guard_msgs in
example (a b : Unit) : a = Unit.unit := by
  chako

namespace MyFoo

inductive Foo (a : Bool) where
  | ctor (h : if a = a then True else True) : Foo a

/--
info: Chako is convinced that the theorem is true.
---
error: unsolved goals
a b : Bool
⊢ Foo a
-/
#guard_msgs in
example (a b : Bool) : Foo a := by
  chako

inductive TwoFoo (a b : Bool) where
  | ctor (h : if a = a then True else True) : TwoFoo a b

/--
info: Chako is convinced that the theorem is true.
---
error: unsolved goals
a b : Bool
⊢ TwoFoo a b
-/
#guard_msgs in
example (a b : Bool) : TwoFoo a b := by
  chako

end MyFoo

namespace Funext

/--
info: Chako is convinced that the theorem is true.
---
error: unsolved goals
⊢ @id = @id
-/
#guard_msgs in
example : @id = @id := by
  chako

end Funext
