import system.io
import data.buffer
import data.buffer.parser

namespace arith

  namespace ast

    structure info := (index : nat)

    inductive term : Type
    | true : info → term
    | false : info → term
    | if_then_else : info → term → term → term → term
    | is_zero : info → term → term
    | zero : info → term
    | succ : info → term → term
    | pred : info → term → term

  end ast

  namespace parser
    def word_import : parser unit := parser.str "import"
    def word_if : parser unit := parser.str "if"
    def word_then : parser unit := parser.str "then"
    def word_else : parser unit := parser.str "else"
    def word_true : parser unit := parser.str "true"
    def word_false  : parser unit := parser.str "false"
    def word_succ : parser unit := parser.str "succ"
    def word_pred : parser unit := parser.str "pred"
    def word_iszero : parser unit := parser.str "iszero"

    def underscore : parser unit := parser.ch '_'
    def apostrophe : parser unit := parser.ch '''
    def backslash : parser unit := parser.ch '\\'
    def bang : parser unit := parser.ch '!'
    def hash : parser unit := parser.ch '#'
    def dollar : parser unit := parser.ch '$'
    def asterisk : parser unit := parser.ch '*'
    def bar : parser unit := parser.ch '|'
    def dot : parser unit := parser.ch '.'
    def semicolon : parser unit := parser.ch ';'
    def colon : parser unit := parser.ch ':'
    def colon2 : parser unit := parser.str "::"
    def eq : parser unit := parser.ch '='
    def eq2 : parser unit := parser.str "=="
    def define : parser unit := parser.str ":="
    def lt : parser unit := parser.ch '<'
    def gt : parser unit := parser.ch '>'

    namespace arrow
      def r : parser unit := parser.str "->"
      def l : parser unit := parser.str "<-"
      def double : parser unit := parser.str "=>"
      def double2 : parser unit := parser.str "==>"
    end arrow

    def between (opening : parser unit) (closing : parser unit) {a : Type} (inside : parser a)
      : parser a := do
      opening,
      result ← inside,
      closing,
      pure result

    namespace bracket
      def square {a : Type} : parser a → parser a :=
        between (parser.ch '[') (parser.ch ']')

      def curly {a : Type} : parser a → parser a :=
        between (parser.ch '{') (parser.ch '}')

      def angle {a : Type} : parser a → parser a :=
        between lt gt

      def square_bar {a : Type} : parser a → parser a :=
        between (parser.str "[|") (parser.str "|]")

      def curly_bar {a : Type} : parser a → parser a :=
        between (parser.str "{|") (parser.str "|}")

      def angle_bar {a : Type} : parser a → parser a :=
        between (parser.str "<|") (parser.str "|>")

    end bracket

    def comment : parser unit :=
      let recur_until_end (until_end : parser unit) :=
          parser.str "*/"
          <|> ( parser.str "/*" *> until_end
                <|> unit.star <$ parser.any_char
              ) *> until_end
      in parser.str "/*" *> parser.fix recur_until_end

    def print_test {α : Type} [has_to_string α]: (string ⊕ α) → io unit
    | (sum.inr ok) := io.print ok
    | (sum.inl err) := io.put_str_ln err

    #eval print_test $ parser.run_string comment "/* /* hello */ */"

  end parser

  def str : string := "hello fron arith"

end arith

def main : io unit :=
  io.put_str_ln arith.str
