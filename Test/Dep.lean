import Test.Util


structure Foo where
  x : Nat
  y : Nat
  h : x = y

/--
info: Proven
---
error: unsolved goals
f : Foo
⊢ f.x = f.y
-/
#guard_msgs in
example (f : Foo) : f.x = f.y := by
  chako_test

/--
info: Proven
---
error: unsolved goals
producer : Nat → Foo
⊢ (producer Nat.zero).x = (producer Nat.zero).y
-/
#guard_msgs in
example (producer : Nat → Foo) : (producer .zero).x = (producer .zero).y := by
  chako_test

/--
info: Unknown
---
error: unsolved goals
xs : List Foo
⊢ ∀ (x : Foo), x ∈ xs → x.x = x.y
-/
#guard_msgs in
example (xs : List Foo) : ∀ x ∈ xs, x.x = x.y := by
  chako_test

/--
info: Proven
---
error: unsolved goals
⊢ 0 = Nat.zero
-/
#guard_msgs in
example : 0 = .zero := by
  chako_test

/--
info: Proven
---
error: unsolved goals
⊢ 1 = Nat.zero.succ
-/
#guard_msgs in
example : 1 = .succ .zero := by
  chako_test

namespace HiddenQuantifiers

inductive Hidden (α : Type) (p : α → Prop) where
  | intro (h : ∀ x, p x) : Hidden α p

structure Val where
  x : Nat
  y : Nat
  h : x = y

namespace Ex1

inductive Bar {α : Type} (p : α → Prop) : α → Prop where
  | intro (x : α) (h : p x) : Bar p x

/--
info: Counterexample
---
error: unsolved goals
⊢ Hidden Val (Bar fun v => v.x = v.y)
-/
#guard_msgs in
example : Hidden Val (Bar (fun v => v.x = v.y)) := by
  chako_test

end Ex1

namespace Ex2

inductive Bar : Val → Prop
  | intro (v : Val) (h : v.x = v.y) : Bar v

/--
info: Counterexample
---
error: unsolved goals
⊢ Hidden Val Bar
-/
#guard_msgs in
example : Hidden Val Bar := by
  chako_test

end Ex2

namespace Ex4

inductive OnlyEmptyLists (α : Type) : Prop where
  | intro (h : ∀ (xs : List α), xs = []) : OnlyEmptyLists α

structure EmptyFin where
  n : Nat
  h : False

/--
info: Proven
---
error: unsolved goals
⊢ OnlyEmptyLists EmptyFin
-/
#guard_msgs in
example : OnlyEmptyLists EmptyFin := by
  chako_test

end Ex4

namespace Ex5

inductive Vect : Nat → Type where
  | nil : Vect .zero
  | cons (x : Nat) (xs : Vect n) : Vect n.succ

def Vect.toList (x : Vect n) : List Nat :=
  match x with
  | .nil => .nil
  | .cons x xs => x :: xs.toList

def mylen : List α → Nat
  | [] => .zero
  | x :: xs => (mylen xs).succ

inductive MyProp : Prop where
  | intro (n : Nat) (x : Vect n) (h : mylen (Vect.toList x) ≠ n) : MyProp

/--
info: Counterexample
---
error: unsolved goals
⊢ MyProp
-/
#guard_msgs in
example : MyProp := by
  chako_test

end Ex5

end HiddenQuantifiers


inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α .zero
  | cons (x : α) (xs : Vec α n) : Vec α n.succ

def Vec.length (x : Vec α n) : Nat := n
def Vec.map (f : α → β) (x : Vec α n) : Vec β n :=
  match x with
  | .nil => .nil
  | .cons x xs => .cons (f x) (map f xs)

/--
info: Proven
---
error: unsolved goals
α : Type
n : Nat
β : Type
xs : Vec α n
f : α → β
⊢ xs.length = (Vec.map f xs).length
-/
#guard_msgs in
example (xs : Vec α n) (f : α → β) : xs.length = (xs.map f).length := by
  chako_test

/--
info: Counterexample
---
error: unsolved goals
α : Type
n : Nat
xs : Vec α n
⊢ xs.length = 0
-/
#guard_msgs in
example (xs : Vec α n) : xs.length = 0 := by
  chako_test

/--
info: Proven
---
error: unsolved goals
α β : Type
m n : Nat
f : α → β
xs : Vec (Vec α m) n
⊢ xs.length = (Vec.map (fun v => Vec.map f v) xs).length
-/
#guard_msgs in
example {f : α → β} (xs : Vec (Vec α m) n) : xs.length = (xs.map (fun v => v.map f)).length := by
  chako_test

/--
info: Counterexample
---
error: unsolved goals
p : Prop
inst : Decidable p
⊢ p
-/
#guard_msgs in
example [inst : Decidable p] : p := by
  chako_test

namespace DepExists

def foo (h : True) : Prop := True

/--
info: Counterexample
---
error: unsolved goals
⊢ ∃ x, True
-/
#guard_msgs in
example : Exists (α := False) fun _ => True := by
  chako_test

/--
info: Proven
---
error: unsolved goals
⊢ Exists foo
-/
#guard_msgs in
example : Exists (α := True) foo := by
  chako_test

/--
info: Counterexample
---
error: unsolved goals
⊢ ∃ x, False
-/
#guard_msgs in
example : Exists (α := True) fun _ => False := by
  chako_test

end DepExists

namespace Unreachable

def head1 (xs : List Nat) (h : xs.isEmpty = false) : Nat :=
  match h2 : xs with
  | [] => absurd h2 (by grind)
  | x :: _ => x

def head2 (xs : List Nat) (h : xs.isEmpty = false) : Nat :=
  match xs with
  | [] => nomatch h
  | x :: _ => x

/--
info: Proven
---
error: unsolved goals
xs : List Nat
h : xs.isEmpty = false
⊢ head1 xs h = head2 xs h
-/
#guard_msgs in
example (xs : List Nat) (h : xs.isEmpty = false) : head1 xs h = head2 xs h := by
  chako_test

end Unreachable
