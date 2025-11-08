module
import Std.Internal.Parsec
import Std.Internal.Parsec.Basic

/-!
This module contains a simple sexpression library to decode Nunchaku models.
-/

namespace Chako

public inductive Sexp where
  | atom (id : String)
  | list (xs : List Sexp)

namespace Sexp

public def toString (s : Sexp) : String :=
  match s with
  | .atom id => id
  | .list xs => "(" ++ String.intercalate " " (xs.map toString) ++ ")"

public instance : ToString Sexp where
  toString xs := toString xs

open Std.Internal.Parsec Std.Internal.Parsec.String

namespace Parser

def idChar : Parser Char := do
  asciiLetter <|> digit <|> pchar '$' <|> pchar '_' <|> pchar '=' <|> pchar '?'
    <|> pchar '-' <|> pchar '>'

mutual

partial def atom : Parser Sexp := do
  let head ← peek!
  if head == '|' then
    skipChar '|'
    let chars ← many (satisfy (· != '|'))
    skipChar '|'
    return .atom <| String.mk ('|' :: chars.toList) ++ "|"
  else
    let chars ← many1 idChar
    return .atom <| String.mk chars.toList


partial def list : Parser Sexp := do
  skipChar '('
  let xs ← many sexpWs
  skipChar ')'
  return .list xs.toList

partial def sexpWs : Parser Sexp := do
  let s ← sexp
  ws
  return s

partial def sexp : Parser Sexp := do
  list <|> atom

end

end Parser

public def parse (input : String) : Except String Sexp :=
  Parser.run Parser.sexp input

end Sexp
end Chako
