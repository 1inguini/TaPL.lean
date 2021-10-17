import system.io
import data.buffer
import data.buffer.parser

namespace arith

  namespace ast

    inductive term : Type
    | true : term
    | false : term
    | if_then_else : term → term → term → term
    | iszero : term → term
    | zero : term
    | succ : term → term
    | pred : term → term

    protected def term.repr : term → string
    | term.true := "true"
    | term.false := "false"
    | (term.if_then_else t₀ t₁ t₂) :=
        "(if " ++ term.repr t₀
        ++ " then " ++ term.repr t₁
        ++ " else " ++ term.repr t₂
        ++ ")"
    | (term.iszero t) := "(iszero "  ++ term.repr t ++ ")"
    | (term.zero) := "zero"
    | (term.succ t) := "(succ " ++ term.repr t ++ ")"
    | (term.pred t) := "(pred " ++ term.repr t ++ ")"

    instance : has_repr term := ⟨term.repr⟩

    protected def term.to_string : term → string
    | term.true := "true"
    | term.false := "false"
    | (term.if_then_else t₀ t₁ t₂) :=
        "if " ++ term.to_string t₀
        ++ " then " ++ term.to_string t₁
        ++ " else " ++ term.to_string t₂
    | (term.iszero t) := "iszero " ++ term.to_string t
    | term.zero := "0"
    | (term.succ t) := "succ " ++ term.to_string t
    | (term.pred t) := "pred " ++ term.to_string t

    instance : has_to_string term := ⟨term.to_string⟩

  end ast

  namespace parser
    protected def print_test {α : Type} [has_repr α]: (string ⊕ α) → io unit
    | (sum.inr ok) := io.put_str_ln $ repr ok
    | (sum.inl err) := io.put_str_ln err

    def between (opening : parser unit) (closing : parser unit) {a : Type} (inside : parser a)
      : parser a := do
      opening,
      result ← inside,
      closing,
      pure result

    def comment : parser unit :=
      let recur_until_end (until_end : parser unit) :=
          parser.str "*/"
          <|> ( parser.str "/*" *> until_end
                <|> unit.star <$ parser.any_char
              ) *> until_end
      in parser.str "/*" *> parser.fix recur_until_end

    -- 全角spaceとかについてはとりあえず考えない
    def spaces : parser unit := parser.many'
      (comment <|> unit.star <$ parser.one_of [' ', '\n', '\t'])

    def lexeme {α : Type} : parser α → parser α := (<* spaces)

    def symbol : string → parser unit :=
      lexeme ∘ parser.str

    def word_import : parser unit := symbol "import"
    def word_if : parser unit := symbol "if"
    def word_then : parser unit := symbol "then"
    def word_else : parser unit := symbol "else"
    def word_true : parser unit := symbol "true"
    def word_false  : parser unit := symbol "false"
    def word_succ : parser unit := symbol "succ"
    def word_pred : parser unit := symbol "pred"
    def word_iszero : parser unit := symbol "iszero"

    def underscore : parser unit := symbol "_"
    def apostrophe : parser unit := symbol "'"
    def backslash : parser unit := symbol "\\"
    def bang : parser unit := symbol "!"
    def hash : parser unit := symbol "#"
    def dollar : parser unit := symbol "$"
    def asterisk : parser unit := symbol "*"
    def bar : parser unit := symbol "|"
    def dot : parser unit := symbol "."
    def semicolon : parser unit := symbol ";"
    def colon : parser unit := symbol ":"
    def colon2 : parser unit := symbol "::"
    def eq : parser unit := symbol "="
    def eq2 : parser unit := symbol "=="
    def define : parser unit := symbol ":="
    def lt : parser unit := symbol "<"
    def gt : parser unit := symbol ">"

    namespace arrow
      def r : parser unit := symbol "->"
      def l : parser unit := symbol "<-"
      def double : parser unit := symbol "=>"
      def double2 : parser unit := symbol "==>"
    end arrow

    namespace bracket
      def paren {a : Type} : parser a → parser a :=
        between (symbol "(") (symbol ")")

      def square {a : Type} : parser a → parser a :=
        between (symbol "[") (symbol "]")

      def curly {a : Type} : parser a → parser a :=
        between (symbol "{") (symbol "}")

      def angle {a : Type} : parser a → parser a :=
        between lt gt

      def square_bar {a : Type} : parser a → parser a :=
        between (symbol "[|") (symbol "|]")

      def curly_bar {a : Type} : parser a → parser a :=
        between (symbol "{|") (symbol "|}")

      def angle_bar {a : Type} : parser a → parser a :=
        between (symbol "<|") (symbol "|>")

    end bracket

    namespace term

      -- Constant
      protected def const (t : ast.term) : parser ast.term := t <$ symbol (to_string t)
      def true : parser ast.term := term.const ast.term.true
      def false : parser ast.term := term.const ast.term.false
      def zero : parser ast.term := term.const ast.term.zero

      -- Unary
      protected def unary
        (symbol_def : string) (mk : ast.term -> ast.term) (inside : parser ast.term)
        : parser ast.term := do
        symbol symbol_def,
        mk <$> inside
      def succ : parser ast.term -> parser ast.term := term.unary "succ" ast.term.succ
      def pred : parser ast.term -> parser ast.term := term.unary "pred" ast.term.pred
      def iszero : parser ast.term -> parser ast.term := term.unary "iszero" ast.term.iszero

      -- if-then-else
      def if_then_else (inside : parser ast.term) : parser ast.term :=
        ast.term.if_then_else
        <$> (symbol "if" *> inside)
        <*> (symbol "then" *> inside)
        <*> (symbol "else" *> inside)

      def term : parser ast.term := parser.fix $ λterm,
         true
        <|> false
        <|> if_then_else term
        <|> zero
        <|> succ term
        <|> pred term
        <|> iszero term
        <|> bracket.paren term

    end term

    def toplevel : parser (list ast.term) :=
      spaces *> parser.many1 (term.term <* semicolon)

  end parser

  namespace eval
    open ast

    -- term may be already normal form before evaluation step
    inductive result : Type
    | already_normal : term → result
    | evaluated : term → result

    namespace small_step

      -- I decided not to reject non-numeric term
      def step : ast.term → result
      | (term.if_then_else term.true t₁ _) := result.evaluated t₁ -- E-IfTrue
      | (term.if_then_else term.false _ t₂) := result.evaluated t₂ -- E-IfFalse
      | t@(term.if_then_else t₀ t₁ t₂) :=
          match step t₀ with
          | (result.already_normal _) := result.already_normal t
          | (result.evaluated t₀') := result.evaluated $ term.if_then_else t₀' t₁ t₂ -- E-If
          end
      | t@(term.succ t₀) :=
          match step t₀ with
          | (result.already_normal _) := result.already_normal t
          | (result.evaluated t₀') := result.evaluated $ term.succ t₀' -- E-Succ
          end
      | (term.pred term.zero) := result.evaluated term.zero -- E-PredZero
      | (term.pred (term.succ t₀)) := result.evaluated term.zero -- E-PredSucc
      | t@(term.pred t₀) :=
          match step t₀ with
          | (result.already_normal _) := result.already_normal t
          | (result.evaluated t₀') := result.evaluated $ term.pred t₀' -- E-Pred
          end
      | (term.iszero term.zero) := result.evaluated $ term.true -- E-IsZeroZero
      | (term.iszero (term.succ _)) := result.evaluated $ term.false -- E-IsZeroSucc
      | t@(term.iszero t₀) :=
          match step t₀ with
          | (result.already_normal _) := result.already_normal t
          | (result.evaluated t₀') := result.evaluated $ term.iszero t₀' -- E-IsZero
          end
      | t := result.already_normal t -- value is always a normal form

    end small_step

  end eval

end arith

def main : io unit := do
  test_str <- io.fs.read_file "test.f" ff,
  io.put_str_ln $ match parser.run arith.parser.toplevel test_str with
  | (sum.inl err) := to_string err
  | (sum.inr x) := to_string x
  end

