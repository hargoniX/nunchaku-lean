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

/--
info: The prover is convinced that the theorem is true.
---
error: unsolved goals
α : Type u_1
xs : List α
⊢ foo xs = id xs
-/
#guard_msgs in
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
  | cons (x : α) (h1 : p x) (xs : List α) (h2 : MyAll p xs) : MyAll p (x :: xs)

/--
info: The prover is convinced that the theorem is true.
---
error: unsolved goals
α : Type
xs : List α
h : xs = []
⊢ MyAll (fun x => False) xs
-/
#guard_msgs in
example (xs : List α) (h : xs = []) : MyAll (fun _ => False) xs := by
  nunchaku

/-
/-
TODO: times out
inductive MyEven : Nat → Prop where
  | zero : MyEven Nat.zero
  | succ : MyEven n → MyEven (Nat.zero.succ.succ + n)

set_option trace.nunchaku true in
example (n : Nat) : MyEven n := by nunchaku
-/
-/

/--
info: The prover is convinced that the theorem is true.
---
error: unsolved goals
α✝ : Type u_1
β✝ : Type u_2
f : α✝ → β✝ → α✝
b : α✝
⊢ List.foldl f b [] = b
-/
#guard_msgs in
example : [].foldl f b = b := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
α : Type u_1
as bs : List α
a b : α
h : as.concat a = bs.concat b
⊢ ¬(as = bs ∧ a = b)
-/
#guard_msgs in
example {as bs : List α} {a b : α} (h : as.concat a = bs.concat b) :
    ¬ (as = bs ∧ a = b) := by
  nunchaku


/--
info: The prover found a counter example
---
error: unsolved goals
α : Type u_1
lt : α → α → Bool
inst✝ : BEq α
a : α
as : List α
⊢ (a :: as).lex [] lt = true
-/
#guard_msgs in
example [BEq α] {a} {as : List α} : List.lex (a :: as) [] lt = true := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
α : Type u_1
β : Type u_2
x : α
xs : List α
f : α → List β
⊢ List.flatMap f (x :: xs) = List.flatMap f xs
-/
#guard_msgs in
example {x : α} {xs : List α} {f : α → List β} :
    List.flatMap f (x :: xs) = List.flatMap f xs := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
α : Type u_1
a : α
as bs : List α
⊢ a ∈ as → ¬a ∈ as ++ bs
-/
#guard_msgs in
example {a : α} {as : List α} (bs : List α) : a ∈ as → ¬ a ∈ as ++ bs := by
  nunchaku


/-

TODO: This has additional pre preconditions in the equation → requires more stuff

set_option trace.nunchaku true in
example [BEq α] : List.isSuffixOf ([] : List α) l = false := by
  nunchaku

example [BEq α] {l : List α} : (l != []) = l.isEmpty := by
  nunchaku
-/

/-
TODO: don't have access to equations for some reason

example {p : α → Bool} {as : List α} {bs : List α} :
    List.filterTR.loop p as bs = bs ++ List.filter p as := by
  nunchaku
  -/

/-

TODO: don't traverse into bodies of theorems

set_option trace.nunchaku true in
example {a : Nat} {as : List Nat} : List.elem a as = false ↔ a ∈ as := by
  nunchaku

-/

/--
info: The prover found a counter example
---
error: unsolved goals
α : Type u_1
β : Type u_2
f : α → β
a b : α
⊢ List.map f [a] = [f b]
-/
#guard_msgs in
example {f : α → β} {a b : α} : List.map f [a] = [f b] := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
α✝ : Type u_1
f : α✝ → α✝
l : List α✝
b : α✝
h : b ∈ List.map f l
⊢ ∃ a, b ∈ l ∧ f a = b
-/
#guard_msgs in
example (h : b ∈ List.map f l) : ∃ a, b ∈ l ∧ f a = b := by
  nunchaku

/--
info: The prover found a counter example
---
error: unsolved goals
α : Type u_1
a : α
l : List α
⊢ a ∈ l ↔ ∃ s t, l = s ++ t
-/
#guard_msgs in
example {a : α} {l : List α} : a ∈ l ↔ ∃ s t : List α, l = s ++ t := by
  nunchaku
