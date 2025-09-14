import Nunchaku

namespace Bar

inductive Tree (α : Type) where
| empty
| node (xs : List (Tree α)) (n : α)

def Tree.map (t : Tree α) (f : α → β) : Tree β :=
  match t with
  | .empty => .empty
  | .node xs n => .node (xs.map (Tree.map · f)) (f n)

/--
info: The prover found a counter example
---
error: unsolved goals
a b : Tree Nat
⊢ a.map Nat.succ = a
-/
#guard_msgs in
example (a b : Tree Nat) : a.map Nat.succ = a := by
  nunchaku

end Bar

namespace Foo

inductive MList (α : Type) where
  | nil
  | cons (x : α) (xs : MList α)

def MList.map (xs : MList α) (f : α → β) : MList β :=
  match xs with
  | .nil => .nil
  | .cons x xs => .cons (f x) (map xs f)

/--
info: The prover found a counter example
---
error: unsolved goals
α : Type
xs : MList α
f : α → α
⊢ xs.map f ≠ xs
-/
#guard_msgs in
example (α : Type) (xs : MList α) (f : α → α) : xs.map f ≠ xs := by
  nunchaku

end Foo

/--
info: The prover found a counter example
---
error: unsolved goals
⊢ List.map id [] ≠ []
-/
#guard_msgs in
example  : [].map id ≠ ([] : List Nat) := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
a : Type u_1
xs : List a
⊢ xs = []
-/
#guard_msgs in
example (xs : List a) : xs = [] := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
α : Type u_1
xs : List α
⊢ List.map id xs ≠ xs
-/
#guard_msgs in
example (xs : List α) : xs.map id ≠ xs := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
α : Type u_1
xs : List (List α)
⊢ List.map id xs ≠ xs
-/
#guard_msgs in
example (xs : List (List α)) : xs.map id ≠ xs := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
α : Type u_1
xs : List (List α)
⊢ List.map (fun x => List.map id x) xs ≠ xs
-/
#guard_msgs in
example (xs : List (List α)) : xs.map (·.map id) ≠ xs := by
  nunchaku

def sumalt : List Nat → Nat :=
  List.foldr Nat.add .zero

/--
info: The prover found a counter example
---
error: unsolved goals
xs : List Nat
h : xs ≠ []
⊢ sumalt xs ≠ Nat.zero
-/
#guard_msgs in
example (xs : List Nat) (h : xs ≠ []) : sumalt xs ≠ .zero := by
  nunchaku

def sumalt' : List Nat → Nat :=
  List.foldr (· + ·) .zero

/--
info: The prover found a counter example
---
error: unsolved goals
x y : Nat
⊢ x + y ≠ x
-/
#guard_msgs in
example (x y : Nat) : x + y ≠ x := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
xs : List Nat
h : xs ≠ []
⊢ sumalt' xs ≠ Nat.zero
-/
#guard_msgs in
example (xs : List Nat) (h : xs ≠ []) : sumalt' xs ≠ .zero := by
  nunchaku

def foo (xs : List α) : List α := id xs

--/--
--info: The prover is convinced that the theorem is true.
-----
--error: unsolved goals
--α : Type u_1
--xs : List α
--⊢ foo xs = id xs
---/
--#guard_msgs in
set_option Elab.async false
set_option trace.nunchaku true in
example (xs : List α) : foo xs = id xs := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
α : Type u_1
f : α → Bool
xs : List α
h : xs = []
⊢ xs.all f = false
-/
#guard_msgs in
example (xs : List α) (h : xs = []) : xs.all f = false := by
  nunchaku

inductive MyAll {α : Type} (p : α → Prop) : List α → Prop where
  | nil : MyAll p []
  | cons (x : α) (xs : List α) (h1 : p x) (h2 : MyAll p xs) : MyAll p (x :: xs)

-- TODO: probably nunchaku bug
set_option trace.nunchaku true in
example (xs : List α) (h : xs = []) : MyAll (fun _ => False) xs := by
  nunchaku

/-
TODO: times out
inductive MyEven : Nat → Prop where
  | zero : MyEven Nat.zero
  | succ : MyEven n → MyEven (Nat.zero.succ.succ + n)

set_option trace.nunchaku true in
example (n : Nat) : MyEven n := by nunchaku
-/

