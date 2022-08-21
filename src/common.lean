-- Common functions shared across languages, such as parser for keywords

import Std.Data.HashMap
import Std.Data.HashSet
open Std

-- def HashSet.singleton {α : Type u} [BEq α] [Hashable α] (a : α) :=
--   HashSet.insert HashSet.empty a

def rw (motive : α → Prop) : a = b → motive a → motive b := @Eq.subst _ motive _ _

-- https://matt.might.net/papers/might2011derivatives.pdf
-- https://dl.acm.org/doi/pdf/10.1145/3360553

private def Fin.max : Fin (Nat.succ k) := 0 - 1
private def Fin.ext : Fin k → Fin (k.succ)
  | ⟨n, h⟩ => ⟨n, Nat.le_succ_of_le h⟩

def Index (ls : List α) : Type := Fin ls.length
def Index.last : Index (l :: ls) := Fin.max
def Index.zero : Index (l :: ls) := ⟨0, Nat.le_add_left 1 ls.length⟩

def isLt (xs ys : List α) {index : Index xs} : ys.length + index.val < (ys ++ xs).length :=
  let goal : index.val < xs.length := index.isLt
  let goal : ys.length + index.val.succ ≤ ys.length + xs.length :=
    Nat.add_le_add_left goal ys.length
  let goal : (ys.length + index.val).succ ≤ ys.length + xs.length :=
    rw (. ≤ ys.length + xs.length) (Nat.add_succ ys.length index.val) goal
  let goal : ys.length + index.val < ys.length + xs.length := Nat.lt_of_succ_le goal
  let goal : ys.length + index.val < (ys ++ xs).length :=
    rw (ys.length + index.val < .) (List.length_append ys xs).symm goal
  goal

def dropUntilIndex : (xs : List α) → Index xs → List α
  | _ :: xs, ⟨0, _⟩ => xs
  | _ :: xs, ⟨Nat.succ k, h⟩ => dropUntilIndex xs ⟨k, Nat.le_of_succ_le_succ h⟩

def dropWithIndex_zero : {xs : List α} →
  dropUntilIndex (x :: xs) ⟨0, Nat.le_add_left 1 xs.length⟩ = xs
  | [] => rfl
  | _ :: _ => rfl

def length_dropWithIndex :
  {xs : List α} → {i : Index xs} →
  (dropUntilIndex xs i).length + i.val + 1 = xs.length
  | x :: xs, ⟨0 , h⟩ =>
    let zero : Index (x :: xs) := ⟨0, h⟩
    let goal := Eq.refl <| (dropUntilIndex (x :: xs) zero).length + 1
    let goal : (dropUntilIndex (x :: xs) zero).length + 1 = xs.length + 1 := goal
    let goal : (dropUntilIndex (x :: xs) zero).length + zero.val + 1 = (x :: xs).length := goal
    goal
  | x :: xs, ⟨Nat.succ k, h⟩ =>
    let i : Index (x :: xs) := ⟨Nat.succ k, h⟩
    let iPrev : Index xs := ⟨k, Nat.le_of_succ_le_succ h⟩
    let prev : (dropUntilIndex xs iPrev).length + iPrev.val + 1 = xs.length := length_dropWithIndex
    let lhs := (dropUntilIndex (x :: xs) i).length + i.val + 1
    let goal := Eq.refl lhs
    let goal : lhs = (dropUntilIndex xs iPrev).length + i.val + 1 := goal
    let goal : lhs = (dropUntilIndex xs iPrev).length + iPrev.val + 1 + 1 := goal
    let goal : lhs = xs.length + 1 := rw (lhs = . + 1) prev goal
    let goal : lhs = (x :: xs).length := goal
    goal

def length_map {α β : Type u} (f : α → β) : (xs : List α) → xs.length = (List.map f xs).length
  | [] => rfl
  | x :: xs =>
    let lhs : xs.length.succ = (x :: xs).length := List.length_cons x xs
    let rhs : xs.length.succ = (List.map f (x :: xs)).length :=
      let goal : (List.map f xs).length.succ = (f x :: List.map f xs).length :=
        List.length_cons (f x) (List.map f xs)
      let goal : (List.map f xs).length.succ = (List.map f (x :: xs)).length := goal
      let goal : xs.length.succ = (List.map f (x :: xs)).length :=
        rw (Nat.succ . = (List.map f (x :: xs)).length) (length_map f xs).symm goal
      goal
    let goal : (x :: xs).length = (List.map f (x :: xs)).length :=
      rfl |>
        rw (. = xs.length.succ) lhs |>
        rw ((x :: xs).length = .) rhs
    goal

private theorem List.cons_get_eq (x : α) (xs : List α) (i : Index xs)
  : (x :: xs).get i.succ = xs.get i := rfl

namespace Parser

--   def between (opening : parser unit) (closing : parser unit) {a : Type} (inside : parser a)
--     : parser a := do
--     opening,
--     result ← inside,
--     closing,
--     pure result

--   def comment : parser unit :=
--     let recur_until_end (until_end : parser unit) :=
--         parser.str "*/"
--         <|> ( parser.str "/*" *> until_end
--               <|> unit.star <$ parser.any_char
--             ) *> until_end
--     in parser.str "/*" *> parser.fix recur_until_end

--   -- Whitespaces
--   -- 全角spaceとかについてはとりあえず考えない
--   def spaces : parser unit := parser.many'
--     (comment <|> unit.star <$ parser.one_of [' ', '\n', '\t'])

--   -- Ignore trailing whitespaces
--   def lexeme {α : Type} : parser α → parser α := (<* spaces)
--   def symbol : string → parser unit := lexeme ∘ parser.str

--   -- Keywords
--   def word.import : parser unit := symbol "import"
--   def word.if : parser unit := symbol "if"
--   def word.then : parser unit := symbol "then"
--   def word.else : parser unit := symbol "else"
--   def word.true : parser unit := symbol "true"
--   def word.false  : parser unit := symbol "false"
--   def word.succ : parser unit := symbol "succ"
--   def word.pred : parser unit := symbol "pred"
--   def word.iszero : parser unit := symbol "iszero"
--   def word.lambda : parser unit := symbol "lambda" <|> symbol "λ"

--   -- Identifier, alphabet followed by alphanum or underscore
--   -- Be careful, it doesn't ignore keywords!
--   def identifier : parser string := lexeme $ do
--     head ← parser.sat char.is_alpha,
--     ⟨rest⟩ ← parser.many_char $ parser.sat (λc, char.is_alphanum c ∨ c = '_'),
--     pure ⟨head :: rest⟩

--   -- Symbols
--   def underscore : parser unit := symbol "_"
--   def apostrophe : parser unit := symbol "'"
--   def backslash : parser unit := symbol "\\"
--   def bang : parser unit := symbol "!"
--   def hash : parser unit := symbol "#"
--   def dollar : parser unit := symbol "$"
--   def asterisk : parser unit := symbol "*"
--   def bar : parser unit := symbol "|"
--   def dot : parser unit := symbol "."
--   def semicolon : parser unit := symbol ";"
--   def colon : parser unit := symbol ":"
--   def colon2 : parser unit := symbol "::"
--   def eq : parser unit := symbol "="
--   def eq2 : parser unit := symbol "=="
--   def define : parser unit := symbol ":="
--   def lt : parser unit := symbol "<"
--   def gt : parser unit := symbol ">"

--   namespace arrow
--     def r : parser unit := symbol "->"
--     def l : parser unit := symbol "<-"
--     def double : parser unit := symbol "=>"
--     def double2 : parser unit := symbol "==>"
--   end arrow

--   namespace bracket

--     def paren {a : Type} : parser a → parser a :=
--       between (symbol "(") (symbol ")")

--     def square {a : Type} : parser a → parser a :=
--       between (symbol "[") (symbol "]")

--     def curly {a : Type} : parser a → parser a :=
--       between (symbol "{") (symbol "}")

--     def angle {a : Type} : parser a → parser a :=
--       between lt gt

--     def square_bar {a : Type} : parser a → parser a :=
--       between (symbol "[|") (symbol "|]")

--     def curly_bar {a : Type} : parser a → parser a :=
--       between (symbol "{|") (symbol "|}")

--     def angle_bar {a : Type} : parser a → parser a :=
--       between (symbol "<|") (symbol "|>")

--   end bracket

--   def terms {α : Type} (termF : parser α → parser α) : parser (list α) :=
--     spaces *> parser.many1 (parser.fix termF <* semicolon)