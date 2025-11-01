import Chako

/-!
Taken from: https://github.com/hargoniX/fil-rb/
-/


namespace RB

inductive Color where
  | black
  | red
  deriving DecidableEq

inductive Set where
  | nil : Set
  | node (left : Set) (data : Nat) (color : Color) (right : Set) : Set

namespace Set

def isEmpty (t : Set) : Bool :=
  match t with
  | .nil => true
  | _ => false

def rootColor (t : Set) : Color :=
  match t with
  | .nil => .black
  | .node _ _ c _ => c

def paintColor (c : Color) (t : Set) : Set :=
  match t with
  | .nil => .nil
  | .node l d _ r => .node l d c r

def isBlack (t : Set) : Bool :=
  match t with
  | .node _ _ .black _ => true
  | _             => false

def baliL (d : Nat) : Set → Set → Set
  | .node (.node t₁ data₁ .red t₂) data₂ .red t₃, right
  | .node t₁ data₁ .red (.node t₂ data₂ .red t₃), right =>
      .node (.node t₁ data₁ .black t₂) data₂ .red (.node t₃ d .black right)
  | left, right => .node left d .black right

def baliR (d : Nat) : Set → Set → Set
  | left, .node t₁ data₁ .red (.node t₂ data₂ .red t₃)
  | left, .node (.node t₁ data₁ .red t₂) data₂ .red t₃ =>
      .node (.node left d .black t₁) data₁ .red (.node t₂ data₂ .black t₃)
  | left, right => .node left d .black right

def ins (d : Nat) (t : Set) : Set :=
  match t with
  | .nil => .node .nil d .red  .nil
  | .node left data .black right =>
    match compare d data with
    | .lt => baliL data (ins d left) right
    | .eq => t
    | .gt => baliR data left (ins d right)
  | .node left data .red right =>
    match compare d data with
    | .lt => .node (ins d left) data .red right
    | .eq => t
    | .gt => .node left data .red (ins d right)

def insert (d : Nat) (t : Set) : Set :=
  paintColor .black (ins d t)

def baldL (d : Nat) : Set → Set → Set
  | .node t₁ data .red t₂, right =>
      .node (.node t₁ data .black t₂) d .red right
  | left, .node t₁ data .black t₂ =>
      baliR d left (.node t₁ data .red t₂)
  | left, .node (.node t₁ data₁ .black t₂) data₂ .red t₃ =>
      .node (.node left d .black t₁) data₁ .red (baliR data₂ t₂ (paintColor .red t₃))
  | left, right => .node left d .red right

def baldR (d : Nat) : Set → Set → Set
  | left, .node t₁ data .red t₂ =>
      .node left d .red (.node t₁ data .black t₂)
  | .node t₁ data .black t₂, right =>
      baliL d (.node t₁ data .red t₂) right
  | .node t₁ data₁ .red (.node t₂ data₂ .black t₃), right =>
      .node (baliL data₁ (paintColor .red t₁) t₂) data₂ .red (.node t₃ d .black right)
  | left, right => .node left d .red right

def appendTrees : Set → Set → Set
  | .nil, t => t
  | t, .nil => t
  | .node left₁ data₁ .red right₁, .node left₂ data₂ .red right₂ =>
    match appendTrees right₁ left₂ with
    | .node left₃ data₃ .red right₃ =>
        .node (.node left₁ data₁ .red left₃) data₃ .red (.node right₃ data₂ .red right₂)
    | t                             => .node left₁ data₁ .red (.node t data₂ .red right₂)
  | .node left₁ data₁ .black right₁, .node left₂ data₂ .black right₂ =>
    match appendTrees right₁ left₂ with
    | .node left₃ data₃ .red right₃ =>
        .node (node left₁ data₁ .black left₃) data₃ .red (.node right₃ data₂ .black right₂)
    | t                             => baldL data₁ left₁ (.node t data₂ .black right₂)
  | t, .node left data .red right => .node (appendTrees t left) data .red right
  | .node left data .red right, t => .node left data .red (appendTrees right t)

def del (d : Nat) : Set → Set
  | .nil => .nil
  | .node left data _ right =>
    match compare d data with
    | .lt =>
      if left.isBlack then
        baldL data (del d left) right
      else
        .node (del d left) data .red right
    | .eq => appendTrees left right
    | .gt =>
      if right.isBlack then
        baldR data left (del d right)
      else
        .node left data .red (del d right)

def erase (d : Nat) (t : Set) : Set :=
  paintColor .black (del d t)

def contains (t : Set) (d : Nat) : Bool :=
  match t with
  | .nil => false
  | .node left data _ right =>
    match compare d data with
    | .lt => left.contains d
    | .eq => true
    | .gt => right.contains d

def inorder : Set → List Nat
  | Set.nil => []
  | Set.node l x _ r => inorder l ++ [x] ++ inorder r

def height (t : Set) : Nat :=
  match t with
  | .nil => 0
  | .node left _ _ right => max (height left) (height right) + 1

inductive Mem (x : Nat) : Set → Prop where
  | here : Mem x (.node left x color right)
  | left (hleft : Mem x left) : Mem x (.node left y color right)
  | right (hright : Mem x right) : Mem x (.node left y color right)

instance : Membership Nat Set where
  mem t x := Mem x t

inductive BST : Set → Prop where
  | nil : BST .nil
  | node (hleft1 : ∀ x ∈ left, x < data) (hleft2 : BST left)
         (hright1 : ∀ x ∈ right, data < x) (hright2 : BST right) : BST (.node left data color right)

def size (t : Set) : Nat :=
  match t with
  | .nil => 0
  | .node l _ _ r => size l + size r + 1

inductive ChildInv : Set → Prop where
  | nil : ChildInv .nil
  | black (hleft : ChildInv left) (hright : ChildInv right) : ChildInv (.node left data .black right)
  | red (hleft1 : ChildInv left) (hleft2 : left.rootColor = .black) (hright1 : ChildInv right)
        (hright2 : right.rootColor = .black) : ChildInv (.node left data .red right)

def blackHeightLeft (t : Set) : Nat :=
  match t with
  | .nil => 0
  | .node left _ color _ =>
    match color with
    | .black => blackHeightLeft left + 1
    | .red => blackHeightLeft left

inductive HeightInv : Set → Prop where
  | nil : HeightInv .nil
  | node (hleft : HeightInv left) (hright : HeightInv right)
         (h : left.blackHeightLeft = right.blackHeightLeft) : HeightInv (.node left data color right)

def empty : Set := .nil

theorem contains_eq_true_iff_mem {set : Set} {x : Nat} (h : set.BST) : set.contains x = true ↔ x ∈ set := by
  sorry

end Set

section Theorems

open Set

theorem BST_insert_of_BST {set : Set} (h : set.BST) : BST (set.insert x) := by
  sorry

theorem BST_erase_of_BST {set : Set} (h : set.BST) : BST (set.erase x) := by
  sorry

theorem childInv_insert_of_rb {set : Set} (h1 : set.BST) (h2 : set.ChildInv) (h3 : set.HeightInv) :
    ChildInv (set.insert x) := by
  sorry

theorem childInv_erase_of_rb {set : Set} (h1 : set.BST) (h2 : set.ChildInv) (h3 : set.HeightInv) :
    ChildInv (set.erase x) := by
  sorry

theorem heightInv_insert_of_rb {set : Set} (h1 : set.BST) (h2 : set.ChildInv) (h3 : set.HeightInv) :
    HeightInv (set.insert x) := by
  sorry

theorem heightInv_erase_of_rb {set : Set} (h1 : set.BST) (h2 : set.ChildInv) (h3 : set.HeightInv) :
    HeightInv (set.erase x) := by
  sorry

theorem contains_eq_false_iff_not_mem {set : Set} (h1 : set.BST) {x : Nat} :
    set.contains x = false ↔ ¬(x ∈ set) := by
  sorry

theorem isEmpty_iff_eq_empty {set : Set} :
    isEmpty set ↔ set = empty := by
  sorry

theorem isEmpty_empty {set : Set} :
    isEmpty (empty : Set) = true := by
  sorry

theorem isEmpty_insert {set : Set} {x : Nat} :
    isEmpty (set.insert x) = false := by
  sorry

theorem not_mem_empty {set : Set} {x : Nat} :
    ¬(x ∈ (empty : Set)) := by
  sorry

theorem contains_empty {set : Set} {x : Nat} :
    contains (empty : Set) x = false := by
  sorry

theorem not_mem_of_isEmpty {set : Set} {a : Nat} :
    set.isEmpty → ¬a ∈ set := by
  sorry

theorem contains_of_isEmpty {set : Set} {a : Nat} :
    set.isEmpty → set.contains a = false := by
  sorry

theorem isEmpty_eq_false_iff_exists_mem {set : Set} :
    set.isEmpty = false ↔ ∃ a, a ∈ set := by
  sorry

theorem isEmpty_eq_false_iff_exists_contains_eq_true {set : Set} :
    set.isEmpty = false ↔ ∃ a, set.contains a = true := by
  sorry

theorem isEmpty_iff_forall_not_mem {set : Set} :
    set.isEmpty = true ↔ ∀ a, ¬a ∈ set := by
  sorry

theorem isEmpty_iff_forall_contains {set : Set} (h1 : set.BST) :
    set.isEmpty = true ↔ ∀ a, set.contains a = false := by
  sorry

theorem mem_insert {set : Set} (h1 : set.BST) {k a : Nat} :
    a ∈ set.insert k ↔ a = k ∨ a ∈ set := by
  sorry

theorem contains_insert {set : Set} (h1 : set.BST) {k a : Nat} :
    (set.insert k).contains a = (a = k ∨ set.contains a) := by
  sorry

theorem mem_of_mem_insert {set : Set} (h1 : set.BST) {k a : Nat} :
    a ∈ set.insert k → a ≠ k → a ∈ set := by
  sorry

theorem contains_of_contains_insert {set : Set} (h1 : set.BST) {k a : Nat} :
    (set.insert k).contains a → a ≠ k → set.contains a := by
  sorry

theorem contains_insert_self {set : Set} (h1 : set.BST) {k : Nat} :
    (set.insert k).contains k := by
  sorry

theorem mem_insert_self {set : Set} (h1 : set.BST) {k : Nat} :
    k ∈ set.insert k := by
  sorry

theorem size_empty {set : Set} :
    (empty : Set).size = 0 := by
  sorry

theorem isEmpty_eq_size_eq_zero {set : Set} :
    set.isEmpty = (set.size == 0) := by
  sorry

open Classical in
theorem size_insert {set : Set} (h1 : set.BST) {k : Nat} :
    (set.insert k).size = if k ∈ set then set.size else set.size + 1 := by
  sorry

theorem size_insert' {set : Set} (h1 : set.BST) {k : Nat} :
    (set.insert k).size = if set.contains k then set.size else set.size + 1 := by
  sorry

theorem size_le_size_insert {set : Set} (h1 : set.BST) {k : Nat} :
    set.size ≤ (set.insert k).size := by
  sorry

theorem size_insert_le {set : Set} (h1 : set.BST) {k : Nat} :
    (set.insert k).size ≤ set.size + 1 := by
  sorry

theorem erase_empty {set : Set} {a : Nat} :
    (empty : Set).erase a = empty := by
  sorry

theorem isEmpty_erase {set : Set} (h1 : set.BST) {k : Nat} :
    (set.erase k).isEmpty = (set.isEmpty || (set.size == 1 && set.contains k)) := by
  sorry

theorem mem_erase {set : Set} (h1 : set.BST) {k a : Nat} :
    a ∈ set.erase k ↔ a ≠ k ∧ a ∈ set := by
  sorry

theorem contains_erase {set : Set} (h1 : set.BST) {k a : Nat} :
    (set.erase k).contains a = (a ≠ k && set.contains a) := by
  sorry

theorem mem_of_mem_erase {set : Set} (h1 : set.BST) {k a : Nat} :
    a ∈ set.erase k → a ∈ set := by
  sorry

theorem contains_of_contains_erase {set : Set} (h1 : set.BST) {k a : Nat} :
    (set.erase k).contains a → set.contains a := by
  sorry

open Classical
theorem size_erase {set : Set} (h1 : set.BST) {k : Nat} :
    (set.erase k).size = if k ∈ set then set.size - 1 else set.size := by
  sorry

theorem size_erase' {set : Set} (h1 : set.BST) {k : Nat} :
    (set.erase k).size = if set.contains k then set.size - 1 else set.size := by
  sorry

theorem size_erase_le {set : Set} (h1 : set.BST) {k : Nat} :
    (set.erase k).size ≤ set.size := by
  sorry

theorem size_le_size_erase {set : Set} (h1 : set.BST) {k : Nat} :
    set.size ≤ (set.erase k).size + 1 := by
  sorry

theorem size_eq_zero_iff_not_mem {set : Set} (h1 : set.BST) :
    set.size = 0 ↔ ∀ x, ¬(x ∈ set) := by
  sorry

theorem size_eq_zero_iff_not_contains {set : Set} (h1 : set.BST) :
    set.size = 0 ↔ ∀ x, set.contains x = false := by
  sorry

theorem size_ne_zero_iff_exists_mem {set : Set} (h1 : set.BST) :
    set.size ≠ 0 ↔ ∃ x, x ∈ set := by
  sorry

theorem size_ne_zero_iff_exists_contains {set : Set} (h1 : set.BST) :
    set.size ≠ 0 ↔ ∃ x, set.contains x = true := by
  sorry

end Theorems

end RB
