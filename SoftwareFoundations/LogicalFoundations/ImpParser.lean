/-
# Lexing and Parsing in Lean
-/

import «SoftwareFoundations».«LogicalFoundations».«Maps»

/-
## Internals
-/

/-
### Lexical Analysis
-/

inductive CharType: Type where
  | whitespace: CharType
  | alpha (c: Char): CharType
  | digit (n: Nat): CharType
  | other (c: Char): CharType

def Char.classify (c: Char): CharType :=
  if c.isWhitespace then .whitespace
  else if c.isAlpha then .alpha c
  else if c.isDigit then .digit c.toString.toNat!
  else .other c

inductive Token: Type where
  | semicolon: Token
  | leftParen: Token
  | rightParen: Token
  | leftBracket: Token
  | rightBracket: Token
  | assign: Token
  | plus: Token
  | minus: Token
  | times: Token
  | eq: Token
  | neq: Token
  | le: Token
  | gt: Token
  | not: Token
  | and: Token
  | while: Token
  | if: Token
  | else: Token
  | for: Token
  | skip: Token
  | break: Token
  | true: Token
  | false: Token
  | id: String → Token
  | num: Nat → Token
deriving Repr

-- TODO: Move `start` into loop so termination is proven
-- TODO: Make more "monadic" and use `do` syntax
-- TODO: Add CLI to run `Imp` programs
partial def String.tokenize (s: String): Except Char (List Token) :=
  let rec loop (acc: List Token) (cs: List CharType): Except Char (List Token) :=
      match cs with
        | .whitespace :: cs => loop acc cs
        | .other ';' :: cs => loop (.semicolon :: acc) cs
        | .other '(' :: cs => loop (.leftParen :: acc) cs
        | .other ')' :: cs => loop (.rightParen :: acc) cs
        | .other '{' :: cs => loop (.leftBracket :: acc) cs
        | .other '}' :: cs => loop (.rightBracket :: acc) cs
        | .other ':' :: .other '=' :: cs => loop (.assign :: acc) cs
        | .other '+' :: cs => loop (.plus :: acc) cs
        | .other '-' :: cs => loop (.minus :: acc) cs
        | .other '*' :: cs => loop (.times :: acc) cs
        | .other '=' :: .other '=' :: cs => loop (.eq :: acc) cs
        | .other '!' :: .other '=' :: cs => loop (.neq :: acc) cs
        | .other '≤' :: cs => loop (.le :: acc) cs
        | .other '>' :: cs => loop (.gt :: acc) cs
        | .other '~' :: cs => loop (.not :: acc) cs
        | .other '&' :: .other '&' :: cs => loop (.and :: acc) cs
        | .other c :: _ => Except.error c
        | .alpha 's' :: .alpha 'k' :: .alpha 'i' :: .alpha 'p' :: cs => loop (.skip :: acc) cs
        | .alpha 'i' :: .alpha 'f' :: cs => loop (.if :: acc) cs
        | .alpha 'e' :: .alpha 'l' :: .alpha 's' :: .alpha 'e' :: cs => loop (.else :: acc) cs
        | .alpha 'f' :: .alpha 'o' :: .alpha 'r' :: cs => loop (.for :: acc) cs
        | .alpha 'w' :: .alpha 'h' :: .alpha 'i' :: .alpha 'l' :: .alpha 'e' :: cs => loop (.while :: acc) cs
        | .alpha 'b' :: .alpha 'r' :: .alpha 'e' :: .alpha 'a' :: .alpha 'k' :: cs => loop (.break :: acc) cs
        | .alpha 't' :: .alpha 'r' :: .alpha 'u' :: .alpha 'e' :: cs => loop (.true :: acc) cs
        | .alpha 'f' :: .alpha 'a' :: .alpha 'l' :: .alpha 's' :: .alpha 'e' :: cs => loop (.false :: acc) cs
        | .alpha c :: cs =>
          let (tok, cs) := id [c] cs
          loop (.id tok :: acc) cs
        | .digit n :: cs =>
          let (tok, cs) := num n cs
          loop (.num tok :: acc) cs
        | [] => Except.ok acc.reverse
  loop [] (s.toList.map Char.classify)
  where
    id (acc: List Char) (cs: List CharType): (String × List CharType) :=
      match cs with
        | .alpha c :: cs => id (c :: acc) cs
        | .digit n :: cs => id ((n.toDigits (base := 10)).reverse ++ acc) cs
        | .other '_' :: cs => id ('_' :: acc) cs
        | _ => (acc.reverse.asString, cs)
    num (acc: Nat) (cs: List CharType): (Nat × List CharType) :=
      match cs with
        | .digit d :: cs => num (acc * 10 + d) cs
        | _ => (acc, cs)

#eval "".tokenize
#eval ";(){}+-*:===!=≤>~&&skipifelseforwhilebreaktruefalse1 32asdfasdf  asfd_42_fooBar".tokenize
#eval "   abc12=3 223*(3+(a+c))  ".tokenize

/-
### Parsing
-/

def Parser (τ: Type) (ε: Type) (σ: Type): Type := List τ → Except ε σ
