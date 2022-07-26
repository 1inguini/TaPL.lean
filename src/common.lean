-- Common functions shared across languages, such as parser for keywords

import Std.Data.HashMap
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

-- inductive Parser.Concrete (Memo : Type) : (α : Type) → Type 1 where
--   | empty {α : Type} : Concrete Memo α
--   | eps {α : Type} (parsed : List α) : Concrete Memo α
--   | term (predicate : Char → Prop) [{a : Char} → Decidable (predicate a)] : Concrete Memo Char
--   | map {α β : Type} (f : α → β) (p : Memo → Concrete Memo α) : Concrete Memo β
--   | isNull {α : Type} (p : Concrete Memo α) : Concrete Memo α
--   | or {α : Type} (p : Memo → Concrete Memo α) (q : Memo → Concrete Memo α)
--     : Concrete Memo α
--   | andThen {α β : Type} (p : Memo → Concrete Memo α) (q : Memo → Concrete Memo β)
--     : Concrete Memo (α × β)

inductive Parser (Token : Type) : (α : Type) → Type 1 where
  | empty {α : Type} : Parser Token α
  | eps {α : Type} (parsed : List α) : Parser Token α
  | term (predicate : Token → Prop) [{a : Token} → Decidable (predicate a)]
    : Parser Token Token
  | map {α β : Type} (f : α → β) (p : Unit → Parser Token α) : Parser Token β
  | isNull {α : Type} (p : Unit → Parser Token α) : Parser Token α
  | or {α : Type} (p : Unit → Parser Token α) (q : Unit → Parser Token α) : Parser Token α
  | andThen {α β : Type} (p : Unit → Parser Token α) (q : Unit → Parser Token β) : Parser Token (α × β)

namespace Parser

  def derive {α : Type} (c : Token) (p : Parser Token α) : Parser Token α := deriveRec (α := α) p c
    where
      deriveRec {α : Type} : Parser Token α → Token → Parser Token α
        | empty, _ => empty
        | eps _, _ => empty
        | term predicate, c => if predicate c then eps [c] else empty
        | map f p, c => map f <| λx => deriveRec (p x) c
        | isNull _, _ => empty
        | Parser.or p q, c => Parser.or (λx => deriveRec (p x) c) (λx => deriveRec (q x) c)
        | andThen (α := α) (β := β) p q, c =>
          let p : _ → Parser Token α := (λx => deriveRec (p x) c)
          let q : _ → Parser Token β := (λx => deriveRec (q x) c)
          Parser.or (λ_ => andThen p q) (λ_ => andThen (λ_ => isNull p) q)

  -- inductive Derive (toType : {α : Type} → ParserRep α → Type)
  --   : {α : Type} → (rep : ParserRep α) → Type where
  --   | empty : Derive toType empty
  --   | eps : Derive toType empty
  --   | term : Derive toType empty
  --   | map {α β : Type} {p : ParserRep α} {f : α → β} (derive : Derive toType p)
  --     : Derive toType (ParserRep.map f p)
  --   | isNull : Derive toType empty
  --   | or {α : Type}
  --       (p : ParserRep α) (q : ParserRep α)
  --       (deriveP : Derive toType p) (deriveQ : Derive toType Q)
  --     : Derive toType (ParserRep.or p q)
  --   | andThen {α β : Type} (p : ParserRep α) (q : ParserRep β) : ParserRep (α × β)

end Parser

-- inductive Parser : (parents : List Type) → (α : Type) → Type 1 where
-- -- private inductive Parser : Refs → Type → Type 1 where
--   -- | up (index : Index parents) : Parser parents (parents.get index)
--   | self {α : Type} {parents : List Type} : Parser (α :: parents) α
--   | empty {α : Type} {parents : List Type} : Parser parents α
--   -- | eps {α : Type} [inst : BEq α] [inst : Hashable α] : HashSet α → Parser' α
--   | eps {α : Type} {parents : List Type} (parsed : List α) : Parser parents α
--   | term {parents : List Type} (predicate : Char → Prop) [{a : Char} → Decidable (predicate a)]
--     : Parser parents Char
--   | map {α β : Type} {parents : List Type}
--     (f : α → β) (p : Parser (β :: parents) α) : Parser parents β
--   | isNull {α : Type} {parents : List Type} (p : Parser (α :: parents) α) : Parser parents α
--   | or {α : Type} {parents : List Type}
--     (p : Parser (α :: parents) α) (q : Parser (α :: parents) α)
--     : Parser parents α
--   | andThen {α β : Type} {parents : List Type}
--     (p : Parser ((α × β) :: parents) α) (q : Parser ((α × β) :: parents) β)
--     : Parser parents (α × β)

namespace Parser

  -- def rebase : (p : Parser (β :: parents) α) → Parser (β :: new) α
  --   -- | up index => λisLt sameType => up ⟨index.val, isLt⟩
  --   | self => self
  --   | empty => empty
  --   | eps parsed => eps parsed
  --   | term predicate => term predicate
  --   | map f p => map f <| rebase p
  --   | isNull p => isNull <| rebase p
  --   | or p q => or (rebase p) (rebase q)
  --   | andThen p q => andThen (rebase p) (rebase q)

  -- def parentDup :
  --   → (p : Parser (bottoms ++ β :: tops) α) → Parser (bottoms ++ β :: β :: tops) α
  --   -- | up index => λisLt sameType => up ⟨index.val, isLt⟩
  --   | [], self => self
  --   | _ :: _, self => self
  --   | _, empty => empty
  --   | _, eps parsed => eps parsed
  --   | _, term predicate => term predicate
  --   | bottoms, map (β := β) f p => map f <| parentDup (β :: bottoms) p
  --   | bottoms, isNull (α := α) p => isNull <| parentDup (α :: bottoms) p
  --   | bottoms, or (α := α) p q =>
  --     let pre := α :: bottoms
  --     or (parentDup pre p) (parentDup pre q)
  --   | bottoms, andThen (α := α) (β := β) p q =>
  --     let pre := (α × β) :: bottoms
  --     andThen (parentDup pre p) (parentDup pre q)

  -- def parentDup : (bottoms : List Type)
  --   → (p : Parser (bottoms ++ β :: tops) α) → Parser (bottoms ++ β :: β :: tops) α
  --   -- | up index => λisLt sameType => up ⟨index.val, isLt⟩
  --   | [], self => self
  --   | _ :: _, self => self
  --   | _, empty => empty
  --   | _, eps parsed => eps parsed
  --   | _, term predicate => term predicate
  --   | bottoms, map (β := β) f p => map f <| parentDup (β :: bottoms) p
  --   | bottoms, isNull (α := α) p => isNull <| parentDup (α :: bottoms) p
  --   | bottoms, or (α := α) p q =>
  --     let pre := α :: bottoms
  --     or (parentDup pre p) (parentDup pre q)
  --   | bottoms, andThen (α := α) (β := β) p q =>
  --     let pre := (α × β) :: bottoms
  --     andThen (parentDup pre p) (parentDup pre q)

  -- def rebase : {α : Type} → {parents : List Type} → {new : List Type}
  --   → (p : Parser parents α)
  --   → match α, parents, new, p with
  --     | _, parent :: parents, α :: new, self => Parser (α :: new) α
  --     | _, parent :: parents, [], self => Parser [] α
  --     | α, _, new, empty => Parser new α
  --     | α, _, new, eps _ => Parser new α
  --     | _, _, new, term _ => Parser new Char
  --     | β, _, new, map f _ => Parser new β
  --     | α, _, new, isNull _ => Parser new α
  --     -- | parent :: parents, new, α, _ => Parser new α
  --   | _, parent :: parents, [], self => empty
  --   | _, parent :: parents, α :: new, self => self
  --   | α, [], [], empty => (empty : Parser [] α)
  --   | α, [], β :: new, empty => (empty : Parser (β :: new) α)
  --   | α, _ :: parents, [], empty => (empty : Parser [] α)
  --   | α, _ :: parents, β :: new, empty => (empty : Parser (β :: new) α)
  --   | α, _, new, eps parsed => eps parsed
  --   | _, _, new, term predicate => term predicate
  --   | β, _, new, map f p => map f p
  --   | α, _, new, isNull p => isNull p

  -- def derive (c : Char) : {α : Type} → Parser parent α → Parser parent α
  --   | _, self => empty
  --   | _, empty => empty
  --   | _, eps _ => empty
  --   | _, term predicate => if predicate c then eps [c] else empty
  --   | _, map f self => map f (map f self)
  --   | _, map f p => map f (derive c p)
  --   -- | _, isNull _ => empty
  --   | _, or self q => let q := derive c q; or (or self q) q
  --   | _, or p q => or (derive c p) (derive c q)
  --   | _, andThen (α := α) (β := β) p q =>
  --     let p : Parser (α × β) α := derive c p
  --     let q : Parser (α × β) β := derive c q
  --     or (andThen p q) (andThen (isNull p) q)

  -- #check (λparents α => (_ : Parser parents α).rec)
  -- def compact {α : Type} {parents : List Type} (p : Parser parents α) : Parser parents α := p.recOn
  --   (motive := λparents α p => Parser parents α)
  --   self -- self
  --   empty -- empty
  --   eps -- eps
  --   term -- term
  --   (λ{α β parents} f p pCompacted => match α, β, parents, f, p with
  --     | _, _, [], f, self => map f self
  --     | _, _, _, f, empty => empty
  --     | _, _, _, f, eps parsed => eps <| List.map f parsed
  --     | _, _, _, f, term predicate => map f <| term predicate
  --     | _, β, α :: parents, f, map g p => map (f ∘ g) <| rebase p
  --     -- (λg p => map (f ∘ g) p)
  --     -- andThen (eps parsed) p => map (λparsed' => f (parsed, parsed')) p
  --     -- | eps parsed => eps <| List.map f parsed
  --   ) -- map
  --   isNull --isNull
  --   (λ_ _ => λ
  --     | p, q => sorry) -- or
  --   andThen

    -- | _, _ :: _, self => self
    -- | _, _, empty => empty
    -- | _, _, eps parsed => eps parsed
    -- | _, _, term predicate => term predicate
    -- | _, _, map f (eps parsed) => eps <| List.map f parsed
    -- | αβ, _, (map f (andThen (eps parsed) p)) => map (λparsed' => f (parsed, parsed')) p
    -- | isNull _ => sorry
    -- | or empty p => compact q
    -- | or p empty => compact p
    -- | andThen empty _ => empty
    -- | andThen _ empty => empty

-- def parseNull : Parser α → List α
--   | empty => []
--   | eps results => results
--   | term _ => []
--   | or p q => parseNull (p ()) ++ parseNull (q ())
--   | andThen p q =>
--     List.bind (parseNull <| p ())
--       (λx => List.bind (parseNull <| q ())
--         (λy => List.pure (x, y)))
--   | map f p => List.map f (parseNull p)
--   | null? p => parseNull p

-- def parse (p : Parser α) : String → List α
--   | ⟨[]⟩ => parseNull p
--   | ⟨c::input⟩ => parse (derive c p) ⟨input⟩


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