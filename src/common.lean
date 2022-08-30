-- Common functions shared across languages, such as Parser for keywords

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

-- namespace Parser

--   @[reducible] def Parser (α : Type) : Type := ReaderT String (StateM Substring) α

--   def between (opening : Parser Unit) (closing : Parser Unit) {α : Type} (inside : Parser α)
--     : Parser α := do
--     opening
--     let result ← inside
--     closing
--     pure result

  -- def comment : Parser unit :=
  --   let recur_until_end (until_end : Parser Unit) :=
  --       Parser.str "*/"
  --       <|> ( Parser.str "/*" *> until_end
  --             <|> unit.star <$ Parser.any_char
  --           ) *> until_end
  --   in Parser.str "/*" *> Parser.fix recur_until_end

--   -- Whitespaces
--   -- 全角spaceとかについてはとりあえず考えない
--   def spaces : Parser unit := Parser.many'
--     (comment <|> unit.star <$ Parser.one_of [' ', '\n', '\t'])

--   -- Ignore trailing whitespaces
--   def lexeme {α : Type} : Parser α → Parser α := (<* spaces)
--   def symbol : string → Parser unit := lexeme ∘ Parser.str

--   -- Keywords
--   def word.import : Parser unit := symbol "import"
--   def word.if : Parser unit := symbol "if"
--   def word.then : Parser unit := symbol "then"
--   def word.else : Parser unit := symbol "else"
--   def word.true : Parser unit := symbol "true"
--   def word.false  : Parser unit := symbol "false"
--   def word.succ : Parser unit := symbol "succ"
--   def word.pred : Parser unit := symbol "pred"
--   def word.iszero : Parser unit := symbol "iszero"
--   def word.lambda : Parser unit := symbol "lambda" <|> symbol "λ"

--   -- Identifier, alphabet followed by alphanum or underscore
--   -- Be careful, it doesn't ignore keywords!
--   def identifier : Parser string := lexeme $ do
--     head ← Parser.sat char.is_alpha,
--     ⟨rest⟩ ← Parser.many_char $ Parser.sat (λc, char.is_alphanum c ∨ c = '_'),
--     pure ⟨head :: rest⟩

--   -- Symbols
--   def underscore : Parser unit := symbol "_"
--   def apostrophe : Parser unit := symbol "'"
--   def backslash : Parser unit := symbol "\\"
--   def bang : Parser unit := symbol "!"
--   def hash : Parser unit := symbol "#"
--   def dollar : Parser unit := symbol "$"
--   def asterisk : Parser unit := symbol "*"
--   def bar : Parser unit := symbol "|"
--   def dot : Parser unit := symbol "."
--   def semicolon : Parser unit := symbol ";"
--   def colon : Parser unit := symbol ":"
--   def colon2 : Parser unit := symbol "::"
--   def eq : Parser unit := symbol "="
--   def eq2 : Parser unit := symbol "=="
--   def define : Parser unit := symbol ":="
--   def lt : Parser unit := symbol "<"
--   def gt : Parser unit := symbol ">"

--   namespace arrow
--     def r : Parser unit := symbol "->"
--     def l : Parser unit := symbol "<-"
--     def double : Parser unit := symbol "=>"
--     def double2 : Parser unit := symbol "==>"
--   end arrow

--   namespace bracket

--     def paren {a : Type} : Parser a → Parser a :=
--       between (symbol "(") (symbol ")")

--     def square {a : Type} : Parser a → Parser a :=
--       between (symbol "[") (symbol "]")

--     def curly {a : Type} : Parser a → Parser a :=
--       between (symbol "{") (symbol "}")

--     def angle {a : Type} : Parser a → Parser a :=
--       between lt gt

--     def square_bar {a : Type} : Parser a → Parser a :=
--       between (symbol "[|") (symbol "|]")

--     def curly_bar {a : Type} : Parser a → Parser a :=
--       between (symbol "{|") (symbol "|}")

--     def angle_bar {a : Type} : Parser a → Parser a :=
--       between (symbol "<|") (symbol "|>")

--   end bracket

--   def terms {α : Type} (termF : Parser α → Parser α) : Parser (list α) :=
--     spaces *> Parser.many1 (Parser.fix termF <* semicolon)