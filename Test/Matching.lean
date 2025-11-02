import Chako

namespace Matching

/--
info: Chako is convinced that the theorem is true.
---
error: unsolved goals
x : Nat
⊢ (Nat.casesOn x true fun x => true) = true
-/
#guard_msgs in
example (x : Nat) :
    Nat.casesOn (motive := fun _ => Bool) x Bool.true (fun _ => Bool.true) = Bool.true := by
  chako

/--
info: Chako found a counter example:
val x := (Nat.succ Nat.zero)
---
error: unsolved goals
x : Nat
⊢ (Nat.casesOn x false fun x => true) = false
-/
#guard_msgs in
example (x : Nat) :
    Nat.casesOn (motive := fun _ => Bool) x Bool.false (fun _ => Bool.true) = Bool.false := by
  chako

/--
info: Chako wasn't able to prove or disprove the theorem.
---
error: unsolved goals
x : List Nat
⊢ (List.casesOn x true fun x x => true) = true
-/
#guard_msgs in
example (x : List Nat) :
    List.casesOn (motive := fun _ => Bool) x Bool.true (fun _ _ => Bool.true) = Bool.true := by
  chako

/--
info: Chako is convinced that the theorem is true.
---
error: unsolved goals
α : Type u_1
x : List α
⊢ (List.casesOn x true fun x x => true) = true
-/
#guard_msgs in
example (x : List α) :
    List.casesOn (motive := fun _ => Bool) x Bool.true (fun _ _ => Bool.true) = Bool.true := by
  chako

/--
info: Chako wasn't able to prove or disprove the theorem.
---
error: unsolved goals
x : List Nat
⊢ (List.casesOn x false fun x x => true) = false
-/
#guard_msgs in
example (x : List Nat) :
    List.casesOn (motive := fun _ => Bool) x Bool.false (fun _ _ => Bool.true) = Bool.false := by
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0
val x := (List.cons $α_0 List.nil)
---
error: unsolved goals
α : Type u_1
x : List α
⊢ (List.casesOn x false fun x x => true) = false
-/
#guard_msgs in
example (x : List α) :
    List.casesOn (motive := fun _ => Bool) x Bool.false (fun _ _ => Bool.true) = Bool.false := by
  chako

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (x : α) (xs : Vec α n) : Vec α (n + 1)

/--
info: Chako found a counter example:
inductive α where | $α_0
val n := (Nat.succ Nat.zero)
val x := (Matching.Vec.cons Nat.zero $α_0 Matching.Vec.nil)
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
  chako

def foo (xs : List α) (f : List α → List α) (g : α → β) (d : β) : β :=
  match xs with
  | [] => d
  | _ :: xs =>
    match f xs with
    | [] => d
    | x :: _ => g x

/--
info: Chako found a counter example:
inductive α where | $α_0 | $α_1
val d := $α_1
val xs := (List.cons $α_1 (List.cons $α_0 List.nil))
---
error: unsolved goals
α : Type u_1
xs : List α
d : α
⊢ foo xs id id d = d
-/
#guard_msgs in
example {xs : List α} {d : α} : foo xs id id d = d := by
  chako

structure MyFin (n : Nat) : Type where
  m : Nat
  h : m < n

/--
info: Chako found a counter example:
val n := (Nat.succ (Nat.succ Nat.zero))
val x := (Matching.MyFin.mk Nat.zero)
---
error: unsolved goals
n : Nat
x : MyFin n
⊢ (MyFin.casesOn x fun x x => false) = true
-/
#guard_msgs in
example {x : MyFin n} : MyFin.casesOn (motive := fun _ => Bool) x (fun _ _ => Bool.false) = Bool.true := by
  chako

def listSameLen (xs ys : List α) : Bool :=
  match xs, ys with
  | [], [] => true
  | _ :: xs, _ :: ys => listSameLen xs ys
  | _, _ => false

/--
info: Chako found a counter example:
inductive α where | $α_0
val xs := (List.cons $α_0 List.nil)
val ys := List.nil
---
error: unsolved goals
α : Type u_1
xs ys : List α
⊢ listSameLen xs ys = true
-/
#guard_msgs in
example (xs ys : List α) : listSameLen xs ys := by
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0
val xs := List.nil
val ys := List.nil
---
error: unsolved goals
α : Type u_1
xs ys : List α
⊢ xs.zip ys ≠ []
-/
#guard_msgs in
example (xs ys : List α) : xs.zip ys ≠ [] := by
  chako

end Matching
