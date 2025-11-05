import Chako

namespace Bar

inductive Tree (α : Type) where
| empty
| node (xs : List (Tree α)) (n : α)

def Tree.map (t : Tree α) (f : α → β) : Tree β :=
  match t with
  | .empty => .empty
  | .node xs n => .node (xs.map (Tree.map · f)) (f n)


/-
bug in unrolling

/--
info: The prover found a counter example
---
error: unsolved goals
a b : Tree Nat
⊢ a.map Nat.succ = a
-/
#guard_msgs in
example (a b : Tree Nat) : a.map Nat.succ = a := by
  chako
-/
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
info: Chako found a counter example:
inductive α where | $α_0
val f := (fun (v_0 : α) . $α_0)
val xs := Foo.MList.nil
---
error: unsolved goals
α : Type
xs : MList α
f : α → α
⊢ xs.map f ≠ xs
-/
#guard_msgs in
example (α : Type) (xs : MList α) (f : α → α) : xs.map f ≠ xs := by
  chako

end Foo

/--
info: Chako found a counter example:
---
error: unsolved goals
⊢ List.map id [] ≠ []
-/
#guard_msgs in
example  : [].map id ≠ ([] : List Nat) := by
  chako

/--
info: Chako found a counter example:
inductive a where | $a_0
val xs := (List.cons $a_0 List.nil)
---
error: unsolved goals
a : Type u_1
xs : List a
⊢ xs = []
-/
#guard_msgs in
example (xs : List a) : xs = [] := by
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0
val xs := List.nil
---
error: unsolved goals
α : Type u_1
xs : List α
⊢ List.map id xs ≠ xs
-/
#guard_msgs in
example (xs : List α) : xs.map id ≠ xs := by
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0
val xs := List.nil
---
error: unsolved goals
α : Type u_1
xs : List (List α)
⊢ List.map id xs ≠ xs
-/
#guard_msgs in
example (xs : List (List α)) : xs.map id ≠ xs := by
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0
val xs := List.nil
---
error: unsolved goals
α : Type u_1
xs : List (List α)
⊢ List.map (fun x => List.map id x) xs ≠ xs
-/
#guard_msgs in
example (xs : List (List α)) : xs.map (·.map id) ≠ xs := by
  chako

def sumalt : List Nat → Nat :=
  List.foldr Nat.add .zero

/--
info: Chako wasn't able to prove or disprove the theorem.
---
error: unsolved goals
xs : List Nat
h : xs ≠ []
⊢ sumalt xs ≠ Nat.zero
-/
#guard_msgs in
example (xs : List Nat) (h : xs ≠ []) : sumalt xs ≠ .zero := by
  chako

def sumalt' : List Nat → Nat :=
  List.foldr (· + ·) .zero

/--
info: Chako found a counter example:
val x := Nat.zero
val y := Nat.zero
---
error: unsolved goals
x y : Nat
⊢ x + y ≠ x
-/
#guard_msgs in
example (x y : Nat) : x + y ≠ x := by
  chako

/--
info: Chako wasn't able to prove or disprove the theorem.
---
error: unsolved goals
xs : List Nat
h : xs ≠ []
⊢ sumalt' xs ≠ Nat.zero
-/
#guard_msgs in
example (xs : List Nat) (h : xs ≠ []) : sumalt' xs ≠ .zero := by
  chako

def foo (xs : List α) : List α := id xs

/--
info: Chako is convinced that the theorem is true.
---
error: unsolved goals
α : Type u_1
xs : List α
⊢ foo xs = id xs
-/
#guard_msgs in
example (xs : List α) : foo xs = id xs := by
  chako

/-
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
  chako
-/
inductive MyAll {α : Type} (p : α → Prop) : List α → Prop where
  | nil : MyAll p []
  | cons (x : α) (h1 : p x) (xs : List α) (h2 : MyAll p xs) : MyAll p (x :: xs)

/--
info: Chako is convinced that the theorem is true.
---
error: unsolved goals
α : Type
xs : List α
h : xs = []
⊢ MyAll (fun x => False) xs
-/
#guard_msgs in
example (xs : List α) (h : xs = []) : MyAll (fun _ => False) xs := by
  chako

/--
info: Chako is convinced that the theorem is true.
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
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0
val a := $α_0
val as := List.nil
val b := $α_0
val bs := List.nil
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
  chako


/--
info: Chako found a counter example:
val $$anon_fun_0 := (fun (v_1 : α) . (fun (v_2 : α) . (if (v_1 = $α_0) then (?__ $$anon_fun_0 v_1 v_2) else (if (and (v_1 = $α_0) (v_2 = $α_0)) then Bool.false else (?__ $$anon_fun_0 v_1 v_2)))))
inductive α where | $α_0
val a := $α_0
val as := List.nil
val inst._@.Test.Mono.2021293408._hygCtx._hyg.8 := (BEq.mk $$anon_fun_0)
val lt := (fun (v_0 : α) . (fun (v_1 : α) . Bool.false))
---
error: unsolved goals
α : Type
lt : α → α → Bool
inst✝ : BEq α
a : α
as : List α
⊢ (a :: as).lex [] lt = true
-/
#guard_msgs in
example {α : Type} {lt : α → α → Bool} [BEq α] {a} {as : List α} : List.lex (a :: as) [] lt = true := by
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0
inductive β where | $β_0
val f := (fun (v_0 : α) . (List.cons $β_0 List.nil))
val x := $α_0
val xs := List.nil
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
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0
val a := $α_0
val as := (List.cons $α_0 List.nil)
val bs := List.nil
---
error: unsolved goals
α : Type u_1
a : α
as bs : List α
⊢ a ∈ as → ¬a ∈ as ++ bs
-/
#guard_msgs in
example {a : α} {as : List α} (bs : List α) : a ∈ as → ¬ a ∈ as ++ bs := by
  chako

section

def myelem (a : Nat) : (l : List Nat) → Bool
  | []    => false
  | b::bs => if a == b then true else myelem a bs

/--
info: Chako found a counter example:
val a := Nat.zero
val as := List.nil
---
error: unsolved goals
a : Nat
as : List Nat
⊢ myelem a as = false ↔ a ∈ as
-/
#guard_msgs in
example {a : Nat} {as : List Nat} : myelem a as = false ↔ a ∈ as := by
  chako

end

/--
info: Chako found a counter example:
inductive α where | $α_0
val as := List.nil
val bs := (List.cons $α_0 List.nil)
val p := (fun (v_0 : α) . Bool.false)
---
error: unsolved goals
α : Type u_1
p : α → Bool
as bs : List α
⊢ List.filterTR.loop p as bs = List.filter p as
-/
#guard_msgs in
example {p : α → Bool} {as : List α} {bs : List α} :
    List.filterTR.loop p as bs = List.filter p as := by
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0
inductive β where | $β_0
val xs := (List.cons (?__ ?l_Prod_elim__1_spec__10_0) List.nil)
---
error: unsolved goals
α β : Type
xs : List ((α → β) × α)
⊢ List.map
      (fun x =>
        match x with
        | (f, s) => f s)
      xs =
    []
-/
#guard_msgs in
example {α β : Type} (xs : List ((α → β) × α)) :
    xs.map (fun (f, s) => f s) = [] := by
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0 | $α_1
inductive β where | $β_0 | $β_1
val a := $α_0
val b := $α_1
val f := (fun (v_0 : α) . (if (v_0 = $α_0) then $β_1 else $β_0))
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
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0 | $α_1
val b := $α_1
val f := (fun (v_0 : α) . $α_1)
val l := (List.cons $α_0 List.nil)
---
error: unsolved goals
α : Type u_1
l : List α
b : α
f : α → α
h : b ∈ List.map f l
⊢ ∃ a, b ∈ l ∧ f a = b
-/
#guard_msgs in
example {f : α → α} (h : b ∈ List.map f l) : ∃ a, b ∈ l ∧ f a = b := by
  chako

/--
info: Chako found a counter example:
inductive α where | $α_0
witness _witness_of := List.nil
val a := $α_0
val l := List.nil
---
error: unsolved goals
α : Type u_1
a : α
l : List α
⊢ a ∈ l ↔ ∃ s t, l = s ++ t
-/
#guard_msgs in
example {a : α} {l : List α} : a ∈ l ↔ ∃ s t : List α, l = s ++ t := by
  chako

namespace FunFlow

/--
info: Chako found a counter example:
val $$anon_fun_0 := (fun (v_1 : α) . (if (v_1 = $α_0) then $β_0 else (?__ $$anon_fun_0 v_1)))
inductive α where | $α_0
inductive β where | $β_0
val f := (fun (v_1 : α) . (if (v_1 = $α_0) then $β_0 else (?__ $$anon_fun_0 v_1)))
---
error: unsolved goals
α β : Type
f : α → β
⊢ (some f).isNone = true
-/
#guard_msgs in
example {α β : Type} (f : α → β) : (some f).isNone := by
  chako

end FunFlow

/--
info: Chako found a counter example:
inductive α where | $α_0 | $α_1
val x := $α_0
val y := $α_1
---
error: unsolved goals
α : Sort u_1
x y : α
⊢ x = y
-/
#guard_msgs in
example (x y : α) : x = y := by
  chako

