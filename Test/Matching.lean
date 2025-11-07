import Test.Util

namespace Matching

inductive Enum where
  | a
  | b

def beq (l r : Enum) : Bool :=
  match l, r with
  | .a, .a => true
  | _, _ => true

/--
info: Counterexample
---
error: unsolved goals
l r : Enum
⊢ beq l r = true ↔ l = r
-/
#guard_msgs in
example (l r : Enum) : beq l r ↔ l = r := by
  chako_test

/--
info: Proven
---
error: unsolved goals
x : Nat
⊢ (Nat.casesOn x true fun x => true) = true
-/
#guard_msgs in
example (x : Nat) :
    Nat.casesOn (motive := fun _ => Bool) x Bool.true (fun _ => Bool.true) = Bool.true := by
  chako_test

/--
info: Counterexample
---
error: unsolved goals
x : Nat
⊢ (Nat.casesOn x false fun x => true) = false
-/
#guard_msgs in
example (x : Nat) :
    Nat.casesOn (motive := fun _ => Bool) x Bool.false (fun _ => Bool.true) = Bool.false := by
  chako_test

/--
info: Proven
---
error: unsolved goals
x : List Nat
⊢ (List.casesOn x true fun x x => true) = true
-/
#guard_msgs in
example (x : List Nat) :
    List.casesOn (motive := fun _ => Bool) x Bool.true (fun _ _ => Bool.true) = Bool.true := by
  chako_test

/--
info: Proven
---
error: unsolved goals
α : Type u_1
x : List α
⊢ (List.casesOn x true fun x x => true) = true
-/
#guard_msgs in
example (x : List α) :
    List.casesOn (motive := fun _ => Bool) x Bool.true (fun _ _ => Bool.true) = Bool.true := by
  chako_test

/--
info: Counterexample
---
error: unsolved goals
x : List Nat
⊢ (List.casesOn x false fun x x => true) = false
-/
#guard_msgs in
example (x : List Nat) :
    List.casesOn (motive := fun _ => Bool) x Bool.false (fun _ _ => Bool.true) = Bool.false := by
  chako_test

/--
info: Counterexample
---
error: unsolved goals
α : Type u_1
x : List α
⊢ (List.casesOn x false fun x x => true) = false
-/
#guard_msgs in
example (x : List α) :
    List.casesOn (motive := fun _ => Bool) x Bool.false (fun _ _ => Bool.true) = Bool.false := by
  chako_test

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (x : α) (xs : Vec α n) : Vec α (n + 1)

/--
info: Counterexample
---
error: unsolved goals
α : Type
n : Nat
x : Vec α n
⊢ (Vec.casesOn x false fun {n} x x => true) = false
-/
#guard_msgs in
example (x : Vec α n) :
    Vec.casesOn (motive := fun _ _ => Bool) x Bool.false (fun _ _ => Bool.true) = Bool.false := by
  chako_test

def foo (xs : List α) (f : List α → List α) (g : α → β) (d : β) : β :=
  match xs with
  | [] => d
  | _ :: xs =>
    match f xs with
    | [] => d
    | x :: _ => g x

/--
info: Counterexample
---
error: unsolved goals
α : Type u_1
xs : List α
d : α
⊢ foo xs id id d = d
-/
#guard_msgs in
example {xs : List α} {d : α} : foo xs id id d = d := by
  chako_test

structure MyFin (n : Nat) : Type where
  m : Nat
  h : m < n

/--
info: Counterexample
---
error: unsolved goals
n : Nat
x : MyFin n
⊢ (MyFin.casesOn x fun x x => false) = true
-/
#guard_msgs in
example {x : MyFin n} : MyFin.casesOn (motive := fun _ => Bool) x (fun _ _ => Bool.false) = Bool.true := by
  chako_test

def listSameLen (xs ys : List α) : Bool :=
  match xs, ys with
  | [], [] => true
  | _ :: xs, _ :: ys => listSameLen xs ys
  | _, _ => false

/--
info: Counterexample
---
error: unsolved goals
α : Type u_1
xs ys : List α
⊢ listSameLen xs ys = true
-/
#guard_msgs in
example (xs ys : List α) : listSameLen xs ys := by
  chako_test

/--
info: Counterexample
---
error: unsolved goals
α : Type u_1
xs ys : List α
⊢ xs.zip ys ≠ []
-/
#guard_msgs in
example (xs ys : List α) : xs.zip ys ≠ [] := by
  chako_test

end Matching
