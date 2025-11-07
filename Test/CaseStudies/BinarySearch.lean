import Chako


@[specialize] def binSearchAux {α : Type u} {β : Type v} (lt : α → α → Bool) (found : Option α → β) (as : Array α) (k : α) :
    (lo : Fin (as.size + 1)) → (hi : Fin as.size) → (lo.1 ≤ hi.1) → β
  | lo, hi, h =>
    let m := (lo.1 + hi.1)/2
    let a := as[m]
    if lt a k then
      if h' : m + 1 ≤ hi.1 then
        binSearchAux lt found as k ⟨m+1, by grind⟩ hi h'
      else found none
    else if lt k a then
      if h' : m = 0 ∨ m - 1 < lo.1 then found none
      else binSearchAux lt found as k lo ⟨m-1, by grind⟩ (by grind)
    else found (some a)
termination_by lo hi => hi.1 - lo.1

@[inline] def binSearch {α : Type} (as : Array α) (k : α) (lt : α → α → Bool) (lo := 0) (hi := as.size - 1) : Option α :=
  if h : lo < as.size then
    let hi := if hi < as.size then hi else as.size - 1
    if w : lo ≤ hi then
      binSearchAux lt id as k ⟨lo, by grind⟩ ⟨hi, by grind⟩ (by grind)
    else
      none
  else
    none

set_option trace.chako true in
example (xs : Array Nat) (h : n ∈ xs) : xs.binSearch n Nat.blt = some n := by
  chako

example (xs : Array Nat) : xs.binSearch n Nat.blt = some y ↔ n = y := by
  chako
