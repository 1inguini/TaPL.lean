-- Common functions shared across languages, such as parser for keywords

-- import Std.Data.HashSet
-- open Std

-- def HashSet.singleton {α : Type u} [BEq α] [Hashable α] (a : α) :=
--   HashSet.insert HashSet.empty a

-- https://matt.might.net/papers/might2011derivatives.pdf
  
namespace Parser

  def Index (ls : List α) : Type := Fin (List.length ls)
  private def Fin.max : Fin (Nat.succ k) := 0 - 1
  def Index.new : Index (l :: ls) := Fin.max
  private def Fin.ext : Fin k → Fin (k.succ)
    | ⟨n, h⟩ => ⟨n, Nat.le_succ_of_le h⟩
  
  private theorem List.cons_get_eq (x : α) (xs : List α) (i : Index xs)
    : (x :: xs).get i.succ = xs.get i := rfl

  structure Ref (tys : List Type) (α : Type) where
    index : Index tys
    same : tys.get index = α
  namespace Ref
    def tyPrepend {xs ys : List Type} (i : Index ys) : xs.length + i.val < (xs ++ ys).length :=
      let goal : i.val < ys.length := i.isLt
      let goal : xs.length + i.val < xs.length + ys.length :=
        Nat.add_le_add_left goal xs.length
      let goal : xs.length + i.val < (xs ++ ys).length :=
        @Eq.subst _ (xs.length + i.val < .) _ _
          (List.length_append xs ys).symm goal
      goal
    
    def shift (newer : List Type) : Ref tys α → Ref (newer ++ tys) α
      | { index := ⟨n, h⟩, same } =>
        let i := ⟨n, h⟩
        let index' := ⟨
          newer.length + n,
          Nat.add_lt_add_left h newer.length |> Eq.subst (List.length_append newer tys).symm
        ⟩
        {
          index := index'
          same := same |> @Eq.subst _ (λx => x = α) _ _
            (getPrepend newer tys i : tys.get i = (newer ++ tys).get ⟨newer.length + i.val, _⟩)
        }
        where

          getPrepend (xs : List Type)
            : (ys : List Type) → (i : Index ys) -- → (h : xs.length + i.val < (xs ++ ys).length)
            → ys.get i = (xs ++ ys).get ⟨xs.length + i.val, tyPrepend i⟩
            | [y], ⟨0, h⟩ --, hxs
              =>
              let zero : Index [y] := ⟨0, h⟩
              let h : xs.length + zero.val < (xs ++ [y]).length := tyPrepend zero
              let rhs : Type := (xs ++ [y]).get ⟨xs.length, h⟩
              let goal : rhs = rhs := rfl
              let goal : y = rhs :=
                let overrun : xs.length < xs.length → False := Nat.not_succ_le_self xs.length
                @Eq.subst _ (. = rhs) ((xs ++ [y]).get ⟨xs.length, h⟩) _
                  (List.get_last overrun) goal
              let goal : ([] ++ [y]).get zero = rhs :=
                let overrun (within : zero.val < [].length) : False := 
                  let h : ¬zero.val < [].length := Nat.not_succ_le_self [].length
                  absurd within h
                @Eq.subst _ (. = rhs) y (([] ++ [y]).get zero)
                  (List.get_last overrun).symm goal
              let goal : [y].get zero = rhs :=
                @Eq.subst ((ls : List Type) ×' Index ls) (λ⟨ls, i⟩ => ls.get i = rhs)
                   ⟨[] ++ [y], ⟨0, _⟩⟩ ⟨[y], zero⟩
                  (PSigma.eta (List.nil_append [y]) rfl) goal
              goal
            | (y :: ys), ⟨0, h⟩ --, h
              =>
              let zero : Index (y :: ys) := ⟨0, h⟩
              let H (ls : List Type) : Prop := xs.length < ls.length
              let h : H (xs ++ y :: ys) := tyPrepend zero
              let i {ls : List Type} (h : H ls) : Index ls := ⟨xs.length, h⟩
              let rhs : Type := (xs ++ y :: ys).get (i h)
              let goal : (xs ++ y :: ys).get (i h) = rhs := rfl
              let hOfAppends : H (xs ++ [y] ++ ys) :=
                let goal : xs.length < xs.length.succ + ys.length :=
                  Nat.le_add_right xs.length.succ ys.length
                let goal : xs.length < xs.length + 1 + ys.length :=
                  @Eq.subst _ (xs.length < . + ys.length) _ _
                    (Nat.add_one xs.length).symm goal
                let goal : xs.length < xs.length + [].length.succ + ys.length :=
                  @Eq.subst _ (xs.length < xs.length + Nat.succ . + ys.length) _ _ List.length_nil.symm goal
                let goal : xs.length < xs.length + [y].length + ys.length := goal
                let goal : xs.length < (xs ++ [y]).length + ys.length :=
                  @Eq.subst _ (xs.length < . + ys.length) _ _
                    (List.length_append xs [y]).symm goal
                let goal : xs.length < (xs ++ [y] ++ ys).length :=
                  @Eq.subst _ (xs.length < .) _ _
                    (List.length_append (xs ++ [y]) ys).symm goal
                goal
              let goal : (xs ++ [y] ++ ys).get (i hOfAppends) = rhs := 
                @Eq.subst ((ls : List Type) ×' H ls) (λ⟨ls, h⟩ => ls.get (i h) = rhs)
                   ⟨xs ++ y :: ys, h⟩ ⟨xs ++ [y] ++ ys, hOfAppends⟩
                  (PSigma.eta (List.append_cons xs y ys) rfl) goal
              let hOfSnoc : H (xs ++ [y]) := 
                let goal : xs.length < xs.length.succ := Nat.succ_le_succ <| Nat.le_refl xs.length
                let goal : xs.length < xs.length + [].length.succ :=
                  @Eq.subst _ (xs.length < xs.length + Nat.succ .) _ _ List.length_nil.symm goal
                let goal : xs.length < xs.length + [y].length := goal
                let goal : xs.length < (xs ++ [y]).length :=
                  @Eq.subst _ (xs.length < .) _ _
                    (List.length_append xs [y]).symm goal
                goal
              let goal : (xs ++ [y]).get (i hOfSnoc) = rhs :=
                @Eq.subst _ (. = rhs) _ _
                  (List.get_append_left (xs ++ [y]) ys _) goal
              let goal : y = rhs :=
                let overrun : (i hOfSnoc).val < xs.length → False := Nat.not_succ_le_self xs.length
                @Eq.subst _ (. = rhs) _ _
                  (List.get_last overrun) goal
              goal
            | (y :: ys), ⟨Nat.succ k, h⟩ =>
              let i : Index (y :: ys) := ⟨Nat.succ k, h⟩
              let iPred : Index ys := ⟨k, Nat.le_of_succ_le_succ i.isLt⟩
              let h : xs.length + i.val < (xs ++ y :: ys).length := tyPrepend i

              let goal
                : ys.get iPred = (xs ++ [y] ++ ys).get ⟨(xs ++ [y]).length + iPred.val, tyPrepend iPred⟩ :=
                getPrepend (xs ++ [y]) ys iPred
              let goal : ys.get iPred = (xs ++ y :: ys).get ⟨(xs ++ [y]).length + iPred.val, _⟩ :=
                let h : (xs ++ [y]).length + iPred.val < (xs ++ y :: ys).length :=
                  let goal : xs.length + iPred.val.succ < (xs ++ y :: ys).length := h
                  let goal : xs.length + (iPred.val + 1) < (xs ++ y :: ys).length :=
                    @Eq.subst _ (xs.length + . < (xs ++ y :: ys).length) _ _
                      (Nat.succ_eq_add_one iPred.val) goal
                  let goal : xs.length + (1 + iPred.val) < (xs ++ y :: ys).length :=
                    @Eq.subst _ (xs.length + . < (xs ++ y :: ys).length) _ _
                      (Nat.add_comm iPred.val 1) goal
                  let goal : xs.length + 1 + iPred.val < (xs ++ y :: ys).length :=
                    @Eq.subst _ (. < (xs ++ y :: ys).length) _ _
                      (Nat.add_assoc xs.length 1 iPred.val).symm goal
                  let goal : xs.length + [y].length + iPred.val < (xs ++ y :: ys).length := goal
                  let goal : (xs ++ [y]).length + iPred.val < (xs ++ y :: ys).length :=
                    @Eq.subst _ (. + iPred.val < (xs ++ y :: ys).length) _ _
                      (List.length_append xs [y]).symm goal
                  goal
                @Eq.subst ((ls : List Type) ×' (xs ++ [y]).length + iPred.val < ls.length)
                  (λ⟨ls, h⟩ => ys.get iPred = ls.get ⟨(xs ++ [y]).length + iPred.val, h⟩)
                  ⟨xs ++ [y] ++ ys, tyPrepend iPred⟩ ⟨xs ++ y :: ys, h⟩
                  (PSigma.eta (List.append_cons xs y ys).symm rfl) goal
              let goal : ys.get iPred = (xs ++ y :: ys).get ⟨xs.length + [y].length + iPred.val, _⟩ :=
                @Eq.subst ((n : Nat) ×' n + iPred.val < (xs ++ y :: ys).length)
                  (λ⟨n, h⟩ => ys.get iPred = (xs ++ y :: ys).get ⟨n + iPred.val, h⟩)
                  ⟨(xs ++ [y]).length, _⟩ ⟨xs.length + [y].length, _⟩
                  (PSigma.eta (List.length_append xs [y]) rfl) goal
              let goal : ys.get iPred = (xs ++ y :: ys).get ⟨xs.length + 1 + iPred.val, _⟩ := goal
              let goal : ys.get iPred = (xs ++ y :: ys).get ⟨xs.length + (1 + iPred.val), _⟩ := 
                @Eq.subst ((n : Nat) ×' n < (xs ++ y :: ys).length)
                  (λ⟨n, h⟩ => ys.get iPred = (xs ++ y :: ys).get ⟨n, h⟩) _ _
                  (PSigma.eta (Nat.add_assoc xs.length 1 iPred.val) rfl) goal
              let goal : ys.get iPred = (xs ++ y :: ys).get ⟨xs.length + (iPred.val + 1), _⟩ :=
                @Eq.subst ((n : Nat) ×' xs.length + n < (xs ++ y :: ys).length)
                  (λ⟨n, h⟩ => ys.get iPred = (xs ++ y :: ys).get ⟨xs.length + n, h⟩) _ _
                  (PSigma.eta (Nat.add_comm 1 iPred.val) rfl) goal
              let goal : ys.get iPred = (xs ++ y :: ys).get ⟨xs.length + iPred.val.succ, _⟩ :=
                @Eq.subst ((n : Nat) ×' xs.length + n < (xs ++ y :: ys).length)
                  (λ⟨n, h⟩ => ys.get iPred = (xs ++ y :: ys).get ⟨xs.length + n, h⟩) _ _
                  (PSigma.eta (Nat.add_one iPred.val) rfl) goal
              let goal : ys.get iPred = (xs ++ y :: ys).get ⟨xs.length + i.val, h⟩ := goal
              let goal : (y :: ys).get i = (xs ++ y :: ys).get ⟨xs.length + i.val, h⟩ := goal
              goal

  #check Eq.subst
  #check False.rec

    def ex : Ref [Char, Nat] Char := Ref.mk (Fin.ofNat 0 : Fin 2) rfl
  end Ref

  private inductive Syntax : List (Type) → Type → Type 1 where
    | empty : Syntax (α :: tys) α
    -- -- | eps {α : Type} [inst : BEq α] [inst : Hashable α] : HashSet α → Parser' α
    | eps : List α → Syntax (α :: tys) α
    | term (predicate : Char → Prop) [{a : Char} → Decidable (predicate a)]
      : Syntax (Char :: tys) Char
    | or (p : Ref pTys α) (q : Ref qTys α)
      (pIsTail : tys.drop (tys.length - pTys.length) = pTys)
      (qIsTail : tys.drop (tys.length - qTys.length) = qTys)
      : Syntax (α :: tys) α
    | andThen (p : Ref pTys α) (q : Ref qtys β)
      (pIsTail : tys.drop (tys.length - pTys.length) = pTys)
      (qIsTail : tys.drop (tys.length - qTys.length) = qTys)
      : Syntax ((α × β) :: tys) (α × β)
    | map : (α → β) → (p : Ref tys α) → Syntax (β :: tys) β
    | isNull : (p : Ref tys α) → Syntax (α :: tys) α

  -- instance [Repr α] [Repr β] [Repr (Syntax tys β)] : Repr (Syntax (ty :: tys) α) where
  --   reprPrec
  --     | Syntax.empty, _ => "empty"
  --     | @Syntax.eps β tys parsed, prec => Repr.addAppParen ("eps " ++ reprArg parsed) prec
  --     | Syntax.term predicate, prec => Repr.addAppParen "term {predicate}" prec

  inductive Memo : List Type → Type 1 where
    | empty : Memo []
    | push : Memo tys → Syntax (α :: tys) α → Memo (α :: tys)
  namespace Memo

    def get : Memo tys → (ref : Ref tys α) → Syntax (tys.drop ref.index.val) α
      | @push tysTail α _ s, Ref.mk ⟨0, _⟩ same => let tys := α :: tysTail
        cast (congrArg (λα => Syntax tys α) same) s
      | @push _ _ memo _, Ref.mk ⟨Nat.succ k, h⟩ same =>
        get memo <| Ref.mk ⟨k, Nat.le_of_succ_le_succ h⟩ same

  -- instance : Repr (Memo []) where
  --   reprPrec
  --     | Memo.empty, _ => "empty"

  -- instance : Repr (Memo (ty :: tys)) where
  --   reprPrec
  --     | Memo.push memo syn, prec => Repr.addAppParen ("push " ++ reprArg memo ++ reprArg syn) prec

  end Memo

  def Parser (tys : List Type) (α : Type) := Memo tys → (Ref (α :: tys) α × Memo (α :: tys))

  def parser (syn : Syntax (α :: tys) α) : Parser tys α := λmemo =>
    let h : 0 < (α :: tys).length :=
      let goal : 0 < [α].length + tys.length := Nat.le_add_right 1 tys.length
      let goal : 0 < ([α] ++ tys).length := Eq.subst (List.length_append [α] tys).symm goal
      let goal : 0 < (α :: tys).length := goal
      goal
    (Ref.mk ⟨0, h⟩ rfl, memo.push syn)
  def empty : Parser tys α := parser Syntax.empty
  def eps : List α → Parser tys α := parser ∘ Syntax.eps
  def term (predicate : Char → Prop) [inst : {a : Char} → Decidable (predicate a)]
    : Parser tys Char := parser (Syntax.term predicate)
  def or (p : Ref pTys α) (q : Ref qTys α)
    (pIsTail : tys.drop (tys.length - pTys.length) = pTys)
    (qIsTail : tys.drop (tys.length - qTys.length) = qTys)
    : Parser tys α := parser (Syntax.or p q pIsTail qIsTail)
  def map (f : α → β) (p : Ref tys α) : Parser tys β :=
    parser (Syntax.map f p)

  def char (c : Char) : Parser tys Char := term (c = .)

  def ex : Parser [Char,Char] Char :=
    let (p, memo) := char 'a' Memo.empty
    let (q, memo) := char 'a' memo
    or p q rfl rfl

  #print ex

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