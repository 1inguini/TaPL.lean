-- Common functions shared across languages, such as parser for keywords

-- import Std.Data.HashSet
-- open Std

-- def HashSet.singleton {α : Type u} [BEq α] [Hashable α] (a : α) :=
--   HashSet.insert HashSet.empty a

-- https://matt.might.net/papers/might2011derivatives.pdf
  
namespace Parser

  structure Ref (α : Type) where
    internal : Nat

  private inductive Syntax : Type → Type 1 where
    | empty : Syntax α
    -- -- | eps {α : Type} [inst : BEq α] [inst : Hashable α] : HashSet α → Parser' α
    | eps : List α → Syntax α
    | term (p : Char → Prop) [{a : Char} → Decidable (p a)] : Syntax Char
    | or : Ref α → Ref α → Syntax α
    | andThen : Ref α → Ref β → Syntax (α × β)
    | map : (α → β) → Ref α → Syntax β
    | null? : Ref α → Syntax α

  inductive Memo : List Type → Type 1 where
    | empty : Memo []
    | push : Memo tys → Syntax α → Memo (α :: tys) 
  namespace Memo

    def get : Memo tys → (i : Fin (List.length tys)) → Syntax (List.get tys i)
      | push _ syn, ⟨0, _⟩ => syn
      | push memo _, ⟨Nat.succ k, h⟩ => get memo ⟨k, Nat.le_of_succ_le_succ h⟩

  end Memo

  -- def Parser (α : Type) := StateM Memo <| Syntax α 

  -- def char (c : Char) : Parser Char := term (c = .)

  -- -- private def printTest {α : Type} [Repr α] : (String ⊕ α) → IO Unit
  -- --   | (Sum.inr ok) => IO.println $ repr ok
  -- --   | (Sum.inl err) => IO.println err

  -- def derive (c : Char) : Parser α → Parser α
  --   | empty => empty
  --   | eps _ => empty
  --   | term predicate => if predicate c then eps [c] else empty
  --   | or p q => or (λ_ => derive c <| p ()) (λ_ => derive c <| q ())
  --   | andThen p q => let p := p ()
  --     or
  --     (λ_ => andThen (λ_ => derive c <| p) q)
  --     (λ_ => andThen (λ_ => null? p) (λ_ => derive c <| q ()))
  --   | map f a => map f <| derive c a
  --   | null? _ => empty

  -- -- def compact : Parser α → Parser α
  -- --   | or empty a => compact a
  -- --   | or a empty => compact a
  -- --   | andThen empty _ => empty
  -- --   | andThen _ empty => empty

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

  -- def sequenceWF : WellFounded (λ(p q : Parser Nat) => sizeOf p < sizeOf q) :=
  --   InvImage.wf sizeOf Nat.lt_wfRel.wf

  -- -- def fix (x : α) (f : (α → β) → α → β) : α → β := f (fix x f)
  -- -- def fix (x : Parser Nat) (f : (Parser Nat → Parser Nat) → Parser Nat → Parser Nat) : Parser Nat → Parser Nat := f (fix x f)
  -- def sequenceOf (c : Char) : Parser Nat :=
  --   let one := map (λ_ => 1) <| char c
  --   (WellFounded.recursion sequenceWF one <|
  --     λ(sequence : Parser Nat)
  --       (loop : (smaller : Parser Nat) → sizeOf smaller < sizeOf sequence → Parser Nat → Parser Nat) _ =>
  --       map (λ(_, n) => Nat.succ n) <| andThen (λ_ => one) (λ_ => loop sequence sorry one)) one

  -- #eval (parse (sequenceOf 'a') "aa")

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

end Parser
export Parser (Parser)