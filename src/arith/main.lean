import system.io
import data.buffer
import data.buffer.parser

namespace arith

  namespace ast

    @[derive decidable_eq]
    inductive term : Type
    | true : term
    | false : term
    | if_then_else : term → term → term → term
    | iszero : term → term
    | zero : term
    | succ : term → term
    | pred : term → term


    private def term.repr : term → string
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

    private def term.to_string : term → string
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

    def term.size : term → ℕ
    | (term.if_then_else t₀ t₁ t₂) := (term.size t₀ + term.size t₁ + term.size t₂).succ
    | (term.iszero t₀) := nat.succ $ term.size t₀
    | (term.succ t₀) := nat.succ $ term.size t₀
    | (term.pred t₀) := nat.succ $ term.size t₀
    | _ := 1

    def term.size_pos : ∀(t : term), 0 < t.size
    | (term.if_then_else t₀ t₁ t₂) := nat.succ_pos (term.size t₀ + term.size t₁ + term.size t₂)
    | (term.iszero t₀) := nat.succ_pos $ term.size t₀
    | (term.succ t₀) := nat.succ_pos $ term.size t₀
    | (term.pred t₀) := nat.succ_pos $ term.size t₀
    | term.true := nat.succ_pos 0
    | term.false := nat.succ_pos 0
    | term.zero := nat.succ_pos 0
  
  end ast

  namespace parser
    private def print_test {α : Type} [has_repr α]: (string ⊕ α) → io unit
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
      private def const (t : ast.term) : parser ast.term := t <$ symbol (to_string t)
      def true : parser ast.term := const ast.term.true
      def false : parser ast.term := const ast.term.false
      def zero : parser ast.term := const ast.term.zero

      -- Unary
      private def unary
        (symbol_def : string) (mk : ast.term -> ast.term) (inside : parser ast.term)
        : parser ast.term := do
        symbol symbol_def,
        mk <$> inside
      def succ : parser ast.term -> parser ast.term := unary "succ" ast.term.succ
      def pred : parser ast.term -> parser ast.term := unary "pred" ast.term.pred
      def iszero : parser ast.term -> parser ast.term := unary "iszero" ast.term.iszero

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

    namespace small_step

      -- I decided not to reject non-numeric term
      def maybe_normal : ast.term → option ast.term -- term may be evaluated or already normal form before evaluation step'
      | (term.if_then_else term.true t₁ _) := pure t₁ -- E-IfTrue
      | (term.if_then_else term.false _ t₂) := pure t₂ -- E-IfFalse
      | t@(term.if_then_else t₀ t₁ t₂) :=
          match maybe_normal t₀ with
          | option.none := option.none
          | (option.some t₀') := pure $ term.if_then_else t₀' t₁ t₂ -- E-If
          end
      | t@(term.succ t₀) :=
          match maybe_normal t₀ with
          | option.none := option.none
          | (option.some t₀') := pure $ term.succ t₀' -- E-Succ
          end
      | (term.pred term.zero) := pure $ term.zero -- E-PredZero
      | (term.pred (term.succ t₀)) := pure $ term.zero -- E-PredSucc
      | t@(term.pred t₀) :=
          match maybe_normal t₀ with
          | option.none := option.none
          | (option.some t₀') := pure $ term.pred t₀' -- E-Pred
          end
      | (term.iszero term.zero) := pure $ term.true -- E-IsZeroZero
      | (term.iszero (term.succ _)) := pure $ term.false -- E-IsZeroSucc
      | t@(term.iszero t₀) :=
          match maybe_normal t₀ with
          | option.none := option.none
          | (option.some t₀') := pure $ term.iszero t₀' -- E-IsZero
          end
      | t := option.none -- value is always a normal form

      def step : ∀(t : term), option {t' : term // t'.size < t.size}
      -- E-IfTrue
      | t@(term.if_then_else term.true t₁ t₂) := pure
          { val := t₁
          , property := 
              let if_size : t.size = 1 + t₁.size + t₂.size + 1 := rfl
                , reorder : 1 + t₁.size + t₂.size + 1 = t₁.size + (1 + t₂.size + 1) :=
                    eq.subst (nat.add_comm 1 t₁.size).symm
                    $ eq.subst (nat.add_assoc t₁.size 1 t₂.size).symm
                    $ eq.subst (nat.add_assoc t₁.size (1 + t₂.size) 1).symm
                    $ rfl
              , zero_lt_sum : 0 < 1 + t₂.size + 1 := nat.zero_lt_succ (1 + t₂.size)
              in
                eq.subst if_size.symm
                $ eq.subst reorder.symm
                $ nat.lt_add_of_pos_right zero_lt_sum
          }
      -- E-IfFalse
      | t@(term.if_then_else term.false t₁ t₂) := pure
          { val := t₂
          , property :=
              let if_size : t.size = 1 + t₁.size + t₂.size + 1 := rfl
                , reorder : 1 + t₁.size + t₂.size + 1 = t₂.size + (1 + t₁.size + 1) :=
                    eq.subst (nat.add_comm (1 + t₁.size) t₂.size).symm
                    $ eq.subst (nat.add_assoc t₁.size (1 + t₂.size) 1).symm
                    $ refl (t₂.size + (1 + t₁.size + 1))
              , zero_lt_sum : 0 < 1 + t₁.size + 1 := nat.zero_lt_succ (1 + t₁.size)
              in
                eq.subst if_size.symm
                $ eq.subst reorder.symm
                $ nat.lt_add_of_pos_right zero_lt_sum
          }
      -- E-If
      | t@(term.if_then_else t₀ t₁ t₂) :=
          match step t₀ with
          | option.none := option.none
          | (option.some ⟨t₀', smaller⟩) := pure $
              { val := term.if_then_else t₀' t₁ t₂
              , property :=
                  let sum_smaller_succ
                      : t₀'.size + (t₁.size + t₂.size).succ < t₀.size + (t₁.size + t₂.size).succ :=
                        nat.add_lt_add_right (smaller : t₀'.size < t₀.size) (t₁.size + t₂.size + 1)
                    , sort₀ (t₀ : term)
                      : (t₀.size + (t₁.size + t₂.size)).succ = t₀.size + (t₁.size + t₂.size).succ :=
                        nat.add_succ t₀.size (t₁.size + t₂.size)
                    , sort₁ (t₀ : term)
                      : t₀.size + t₁.size + t₂.size = t₀.size + (t₁.size + t₂.size) :=
                        nat.add_assoc t₀.size t₁.size t₂.size
                    , to_if_then_else (t₀ : term)
                      : (t₀.size + t₁.size + t₂.size).succ = (term.if_then_else t₀ t₁ t₂).size :=
                        rfl
                  in
                    eq.subst (to_if_then_else t₀)
                    $ eq.subst (to_if_then_else t₀')
                    $ eq.subst (sort₁ t₀).symm
                    $ eq.subst (sort₁ t₀').symm
                    $ eq.subst (sort₀ t₀).symm
                    $ eq.subst (sort₀ t₀').symm
                    $ sum_smaller_succ
              }
          end
      -- E-Succ
      | t@(term.succ t₀) :=
          match step t₀ with
          | option.none := option.none
          | (option.some ⟨t₀', smaller⟩) := pure $
              { val := term.succ t₀'
              , property :=
                  eq.subst (rfl : t.size = t₀.size.succ)
                  $ eq.subst (rfl : t₀'.succ.size = t₀'.size.succ)
                  $ nat.succ_le_succ
                  $ smaller
              }
          end
      -- E-PredZero
      | t@(term.pred term.zero) := pure 
          { val := term.zero
          , property :=
              eq.subst (rfl : term.zero.size = 1)
              $ eq.subst (rfl : t.size = 2)
              $ nat.succ_le_succ
              $ nat.zero_lt_succ 0
          }
      -- E-PredSucc
      | t@(term.pred (term.succ t₀)) := pure 
          { val := term.zero
          , property :=
              eq.subst (rfl : t.size = t₀.size.succ.succ)
              $ eq.subst (rfl : term.zero.size = 1)
              $ nat.succ_le_succ
              $ nat.succ_pos t₀.size
          }
      -- E-Pred
      | t@(term.pred t₀) := 
          match step t₀ with
          | option.none := option.none
          | (option.some ⟨t₀', smaller⟩) := pure $
              { val := term.pred t₀'
              , property :=
                  eq.subst (rfl : t.size = t₀.size.succ)
                  $ eq.subst (rfl : t₀'.pred.size = t₀'.size.succ)
                  $ nat.succ_le_succ
                  $ smaller
              }
          end
      -- E-IsZeroZero
      | t@(term.iszero term.zero) := pure
          { val := term.true
          , property :=
              eq.subst (rfl : term.true.size = 1)
              $ eq.subst (rfl : t.size = 2)
              $ nat.succ_le_succ
              $ nat.zero_lt_succ 0
          }
      -- E-IsZeroSucc
      | t@(term.iszero (term.succ t₀)) := pure
          { val := term.false
          , property :=
              eq.subst (rfl : term.false.size = 1)
              $ eq.subst (rfl : t.size = t₀.size.succ.succ)
              $ nat.succ_le_succ
              $ nat.zero_lt_succ t₀.size
          }
      -- E-IsZero
      | t@(term.iszero t₀) :=
          match step t₀ with
          | option.none := option.none
          | (option.some ⟨t₀', smaller⟩) := pure $
              { val := term.iszero t₀'
              , property :=
                  eq.subst (rfl : t.size = t₀.size.succ)
                  $ eq.subst (rfl : t₀'.iszero.size = t₀'.size.succ)
                  $ nat.succ_le_succ
                  $ smaller
              }
          end
      -- value is always a normal form
      | t := option.none
      
      --   : ∀(t : term), {t' : term // t'.size < t.size ∨ t' = t }
      -- | t@term.true :=
      --     { val := t
      --     , property := λ(not_normal : maybe_normal t = option.some t),
      --         let no : option.none = option.some t := 
      --           eq.trans (rfl : maybe_normal t = option.none) not_normal
      --         in absurd no (λh, option.no_confusion h)
      --     }
      -- | t@term.false :=
      --     { val := t
      --     , property := λ(not_normal : maybe_normal t = option.some t),
      --         let no : option.none = option.some t := 
      --           eq.trans (rfl : maybe_normal t = option.none) not_normal
      --         in absurd no (λh, option.no_confusion h)
      --     }
      -- | t@(term.iszero t₀) :=
      --     { val := t
      --     , property := λ(not_normal : maybe_normal t = option.some t),
      --         let no : option.none = option.some t := 
      --           eq.trans (rfl : maybe_normal t = option.none) not_normal
      --         in absurd no (λh, option.no_confusion h)
      --     }
      -- | t@term.zero :=
      --     { val := t
      --     , property := λ(not_normal : maybe_normal t = option.some t),
      --         let no : option.none = option.some t := 
      --           eq.trans (rfl : maybe_normal t = option.none) not_normal
      --         in absurd no (λh, option.no_confusion h)
      --     }

      private def loop : ∀(t : term) (loop : ∀(smaller : term), smaller.size < t.size → term), term
      | t@term.true := λ_, t
      | t@term.false := λ_, t
      | t@term.zero := λ_, t
      | t := λloop,
          let ⟨t', decreases⟩ := step_decreases_size t
          in match option.decidable_eq (step t) (option.some t') with
          | (decidable.is_false _) := t
          | (decidable.is_true evaluated) := loop t' $ decreases evaluated
          end

        /- match step t with -/
        /- | option.none := t -/
        /- | (option.some term.true) := term.true -/
        /- | (option.some term.false) := term.true -/
        /- | (option.some term.zero) := term.true -/
        /- | (option.some t'@(term.iszero t₀)) := -/
        /-     let p₀ : t₀.iszero.size = t₀.size.succ := rfl -/
        /-       , p₁ : t₀.iszero.size = t₀.size.succ := rfl -/
        /-     in loop t' $ begin -/
        /-       rw p₀, -/
        /-     end -/

      def eval : term → term :=
        well_founded.fix _ loop

      #check eval term.zero
      /- | option.none := option.none -/
      /- | (option.some t) := -/
      /-     have (step t).sizeof < 1 + t.sizeof, -/
      /-     from _, -/
      /-     loop $ step t -/

      /- -- def eval : ast.term → ast.term := loop ∘ step -/
      /- def eval (t : term) : term := -/
      /-   match eval' $ option.some t with -/
      /-   | option.some t' := t' -/
      /-   | option.none := t -/
      /-   end -/

    end small_step

  end eval

end arith

def main : io unit := do
  test_str <- io.fs.read_file "test.f" ff,
  io.put_str_ln $ match parser.run arith.parser.toplevel test_str with
  | (sum.inl err) := to_string err
  | (sum.inr x) := to_string $ functor.map arith.eval.small_step.eval x
  end

