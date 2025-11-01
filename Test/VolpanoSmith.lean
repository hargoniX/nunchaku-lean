import Chako

/-!
Based on:
- https://www.isa-afp.org/entries/VolpanoSmith.html#
- https://www.tcs.ifi.lmu.de/mitarbeiter/jasmin-blanchette/itp2010-nitpick.pdf
-/

abbrev PartialMap (α β : Type) : Type := α → Option β

open Classical in
noncomputable def PartialMap.update (map : PartialMap α β) (k : α) (v : Option β) : PartialMap α β :=
  fun x => if x = k then v else map x

abbrev Ident : Type := Nat

inductive Value where
  | bool (b : Bool)
  | nat (n : Nat)

instance : BEq Value where
  beq
    | .bool b1, .bool b2 => b1 == b2
    | .bool b1, .nat n1 => false
    | .nat n1, .bool b1 => false
    | .nat n1, .nat n2 => n1 == n2

inductive Bop where
  | eq
  | and
  | less
  | add
  | sub

def Bop.apply (bop : Bop) (lhs rhs : Value) : Option Value :=
  match bop, lhs, rhs with
  | .eq, lhs, rhs => some <| .bool <| lhs == rhs
  | .and, .bool lhs, .bool rhs => some <| .bool <| lhs && rhs
  | .less, .nat lhs, .nat rhs => some <| .bool <| lhs < rhs
  | .add, .nat lhs, .nat rhs => some <| .nat <| lhs + rhs
  | .sub, .nat lhs, .nat rhs => some <| .nat <| lhs - rhs
  -- Cannot yet handle default equations
  --| _, _, _ => some <| .nat 0
  | .sub, .bool _, .bool _ => some <| .nat 0
  | .sub, .nat _, .bool _ => some <| .nat 0
  | .sub, .bool _, .nat _ => some <| .nat 0
  | .add, .bool _, .bool _ => some <| .nat 0
  | .add, .nat _, .bool _ => some <| .nat 0
  | .add, .bool _, .nat _ => some <| .nat 0
  | .less, .bool _, .bool _ => some <| .nat 0
  | .less, .nat _, .bool _ => some <| .nat 0
  | .less, .bool _, .nat _ => some <| .nat 0
  | .and, .nat _, .nat _ => some <| .nat 0
  | .and, .nat _, .bool _ => some <| .nat 0
  | .and, .bool _, .nat _ => some <| .nat 0

inductive Expr where
  | val (val : Value)
  | var (ident : Ident)
  | bin (lhs : Expr) (op : Bop) (rhs : Expr)

abbrev State := PartialMap Ident Value

def Expr.interpret (e : Expr) (s : State) : Option Value :=
  match e with
  | .val v => some v
  | .var i => s i
  | .bin lhs op rhs =>
    match lhs.interpret s with
    | none => none
    | some lval =>
      match rhs.interpret s with
      | none => none
      | some rval => op.apply lval rval

inductive Com where
  | skip
  | assign (ident : Ident) (val : Expr)
  | seq (lhs rhs : Com)
  | cond (discr : Expr) (t e : Com)
  | while (discr : Expr) (body : Com)

set_option hygiene false in
notation "("c1", "s1")" " ⇝ " "("c2", "s2")" => Red (c1, s1) (c2, s2)

inductive Red : Com × State → Com × State → Prop where
  | assign : (.assign v e, s) ⇝ (.skip, s.update v (e.interpret s))
  | seq (h : (c1, s1) ⇝ (c1', s1')) : (.seq c1 c2, s1) ⇝ (.seq c1' c2, s1')
  | skipseq : (.seq .skip c, s) ⇝ (c, s)
  | ifpos (h : d.interpret s = some (.bool true)) : (.cond d t e, s) ⇝ (t, s)
  | ifneg (h : d.interpret s = some (.bool false)) : (.cond d t e, s) ⇝ (e, s)
  | whilepos (h : d.interpret s = some (.bool true)) : (.while d b, s) ⇝ (.seq b (.while d b), s)
  | whileneg (h : d.interpret s = some (.bool false)) : (.while d b, s) ⇝ (.skip, s)

inductive RTC {α : Type u} (R : α → α → Prop) (a : α) : α → Prop
  | refl : RTC R a a
  | tail (b c) (hab : RTC R a b) (hbc : R b c) : RTC R a c

notation "("c1", "s1")" " ⇝* " "("c2", "s2")" => RTC Red (c1, s1) (c2, s2)

inductive SecLevel where
  | low
  | high

abbrev TypeEnv : Type := PartialMap Ident SecLevel

set_option hygiene false in
notation Γ " ⊢ " e " : " τ => SecExprTyping Γ e τ

inductive SecExprTyping (Γ : TypeEnv) : (e : Expr) → (τ : SecLevel) → Prop where
  | var (h : Γ v = some lvl) : Γ ⊢ .var v : lvl
  | bop1 (h1 : Γ ⊢ e1 : .low) (h2 : Γ ⊢ e2 : .low) : Γ ⊢ .bin e1 op e2 : .low
  | bop2 (h1 : Γ ⊢ e1 : .high) (h2 : Γ ⊢ e2 : lvl) : Γ ⊢ .bin e1 op e2 : .high
  | bop3 (h1 : Γ ⊢ e1 : lvl) (h2 : Γ ⊢ e2 : .high) : Γ ⊢ .bin e1 op e2 : .high

set_option hygiene false in
notation "(" Γ " , " σ ")" " ⊢ " τ => SecComTyping Γ σ τ

-- This is the wrong definition from Blanchette
inductive SecComTyping (Γ: TypeEnv) : (lvl : SecLevel) → (com : Com) → Prop where
  | skip : (Γ, σ) ⊢ .skip
  | assignH (h : Γ v = some .high) : (Γ, σ) ⊢ .assign v e
  | assignL (h1 : Γ ⊢ e : .low) (h2 : Γ v = some .low) : (Γ, .low) ⊢ .assign v e
  | seq (h : (Γ, σ) ⊢ c1) : (Γ, σ) ⊢ .seq c1 c2
  | cond (h1 : Γ ⊢ b : σ) (h2 : (Γ, σ) ⊢ c1) (h3 : (Γ, σ) ⊢ c2) : (Γ, σ) ⊢ .cond b c1 c2
  | while (h1 : Γ ⊢ b : σ) (h2 : (Γ, σ) ⊢ c) : (Γ, σ) ⊢ .while b c
  | cast (h : (Γ, .high) ⊢ c) : (Γ, .low) ⊢ c

-- TODO: currently broken due to lambda lifting

/-
set_option trace.nunchaku true in
example (Γ : TypeEnv) (c : Com) (s s' : State) (h : ((Γ, .high) ⊢ c) ∧ (c, s) ⇝* (.skip, s')) :
    ∀ v, Γ v = some .low → s v = s' v := by
  nunchaku
  -/
