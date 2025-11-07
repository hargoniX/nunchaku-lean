theory Scratch imports Main begin

section ‹The Language›

subsection ‹Variables and Values›

type_synonym vname = string ― ‹names for variables›

datatype val
  = Bool bool      ― ‹Boolean value›
  | Intg int       ― ‹integer value›

abbreviation "true == Bool True"
abbreviation "false == Bool False"

subsection ‹Expressions and Commands›

datatype bop = Eq | And | Less | Add | Sub     ― ‹names of binary operations›

datatype expr
  = Val val                                          ― ‹value›
  | Var vname                                        ― ‹local variable›
  | BinOp expr bop expr    (‹_ «_» _› [80,0,81] 80)  ― ‹binary operation›


text ‹Note: we assume that only type correct expressions are regarded
  as later proofs fail if expressions evaluate to None due to type errors.
  However there is [yet] no typing system›

fun binop :: "bop ⇒ val ⇒ val ⇒ val option"
where "binop Eq v⇩1 v⇩2               = Some(Bool(v⇩1 = v⇩2))"
  | "binop And (Bool b⇩1) (Bool b⇩2)  = Some(Bool(b⇩1 ∧ b⇩2))"
  | "binop Less (Intg i⇩1) (Intg i⇩2) = Some(Bool(i⇩1 < i⇩2))"
  | "binop Add (Intg i⇩1) (Intg i⇩2)  = Some(Intg(i⇩1 + i⇩2))"
  | "binop Sub (Intg i⇩1) (Intg i⇩2)  = Some(Intg(i⇩1 - i⇩2))"

  | "binop bop v⇩1 v⇩2                = Some(Intg(0))"


datatype com
  = Skip
  | LAss vname expr        (‹_:=_› [70,70] 70)  ― ‹local assignment›
  | Seq com com            (‹_;;/ _› [61,60] 60)
  | Cond expr com com      (‹if '(_') _/ else _› [80,79,79] 70)
  | While expr com         (‹while '(_') _› [80,79] 70)


fun fv :: "expr ⇒ vname set" ― ‹free variables in an expression›
where
  FVc: "fv (Val V) = {}"
  | FVv: "fv (Var V) = {V}"
  | FVe: "fv (e1 «bop» e2) = fv e1 ∪ fv e2"


subsection ‹State›

type_synonym state = "vname ⇀ val"


text ‹‹interpret› silently assumes type correct expressions,
  i.e. no expression evaluates to None›

fun "interpret" :: "expr ⇒ state ⇒ val option" (‹⟦_⟧_›)
where Val: "⟦Val v⟧ s = Some v"
  | Var: "⟦Var V⟧ s = s V"
  | BinOp: "⟦e⇩1«bop»e⇩2⟧ s = (case ⟦e⇩1⟧ s of None ⇒ None
    | Some v⇩1 ⇒ (case ⟦e⇩2⟧ s of None ⇒ None
                           | Some v⇩2 ⇒ binop bop v⇩1 v⇩2))"

subsection ‹Small Step Semantics›

inductive red :: "com * state ⇒ com * state ⇒ bool"
and red' :: "com ⇒ state ⇒ com ⇒ state ⇒ bool"
   (‹((1⟨_,/_⟩) →/ (1⟨_,/_⟩))› [0,0,0,0] 81)
where
  "⟨c1,s1⟩ → ⟨c2,s2⟩ == red (c1,s1) (c2,s2)" |
  RedLAss:
  "⟨V:=e,s⟩ → ⟨Skip,s(V:=(⟦e⟧ s))⟩"

  | SeqRed:
  "⟨c⇩1,s⟩ → ⟨c⇩1',s'⟩ ⟹ ⟨c⇩1;;c⇩2,s⟩ → ⟨c⇩1';;c⇩2,s'⟩"

  | RedSeq:
  "⟨Skip;;c⇩2,s⟩ → ⟨c⇩2,s⟩"

  | RedCondTrue:
  "⟦b⟧ s = Some true ⟹ ⟨if (b) c⇩1 else c⇩2,s⟩ → ⟨c⇩1,s⟩"

  | RedCondFalse:
  "⟦b⟧ s = Some false ⟹ ⟨if (b) c⇩1 else c⇩2,s⟩ → ⟨c⇩2,s⟩"

  | RedWhileTrue:
  "⟦b⟧ s = Some true ⟹ ⟨while (b) c,s⟩ → ⟨c;;while (b) c,s⟩"

  | RedWhileFalse:
  "⟦b⟧ s = Some false ⟹ ⟨while (b) c,s⟩ → ⟨Skip,s⟩"

lemmas red_induct = red.induct[split_format (complete)]

abbreviation reds ::"com ⇒ state ⇒ com ⇒ state ⇒ bool"
   (‹((1⟨_,/_⟩) →*/ (1⟨_,/_⟩))› [0,0,0,0] 81) where
  "⟨c,s⟩ →* ⟨c',s'⟩ ==  red⇧*⇧* (c,s) (c',s')"

section ‹Security types›

subsection ‹Security definitions›


datatype secLevel = Low | High

type_synonym typeEnv = "vname ⇀ secLevel"

inductive secExprTyping :: "typeEnv ⇒ expr ⇒ secLevel ⇒ bool" (‹_ ⊢ _ : _›)
where typeVal:  "Γ ⊢ Val V : lev"

  | typeVar:    "Γ Vn = Some lev ⟹ Γ ⊢ Var Vn : lev"

  | typeBinOp1: "⟦Γ ⊢ e1 : Low; Γ ⊢ e2 : Low⟧ ⟹ Γ ⊢ e1 «bop» e2 : Low"

  | typeBinOp2: "⟦Γ ⊢ e1 : High; Γ ⊢ e2 : lev⟧ ⟹ Γ ⊢ e1 «bop» e2 : High"

  | typeBinOp3: "⟦Γ ⊢ e1 : lev; Γ ⊢ e2 : High⟧ ⟹ Γ ⊢ e1 «bop» e2 : High"



inductive secComTyping :: "typeEnv ⇒ secLevel ⇒ com ⇒ bool" (‹_,_ ⊢ _›)
where typeSkip:  "Γ,T ⊢ Skip"

  | typeAssH:    "Γ V = Some High ⟹ Γ,T ⊢ V := e"

  | typeAssL:    "⟦Γ ⊢ e : Low; Γ V = Some Low⟧ ⟹ Γ,Low ⊢ V := e"

  | typeSeq:     "⟦Γ,T ⊢ c1⟧ ⟹ Γ,T ⊢ c1;;c2"

  | typeWhile:   "⟦Γ ⊢ b : T; Γ,T ⊢ c⟧ ⟹ Γ,T ⊢ while (b) c"

  | typeIf:      "⟦Γ ⊢ b : T; Γ,T ⊢ c1; Γ,T ⊢ c2⟧ ⟹ Γ,T ⊢ if (b) c1 else c2"

  | typeConvert: "Γ,High ⊢ c ⟹ Γ,Low ⊢ c"

lemma foo : "(Γ, High ⊢ c ∧ ⟨c, s⟩  →* ⟨Skip, s'⟩) ⟶ (∀ v. Γ v = Some Low) ⟶ s v = s v'"
  nitpick
