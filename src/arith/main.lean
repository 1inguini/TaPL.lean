import system.io
import data.buffer
import data.buffer.parser

namespace arith

  @[derive decidable_eq]
  inductive term : Type
  | true : term
  | false : term
  | if_then_else : term → term → term → term
  | iszero : term → term
  | zero : term
  | succ : term → term
  | pred : term → term

  namespace term 
  
    private def repr : term → string
    | true := "true"
    | false := "false"
    | (if_then_else t₀ t₁ t₂) :=
        "(if " ++ repr t₀
        ++ " then " ++ repr t₁
        ++ " else " ++ repr t₂
        ++ ")"
    | (iszero t) := "(iszero "  ++ repr t ++ ")"
    | (zero) := "zero"
    | (succ t) := "(succ " ++ repr t ++ ")"
    | (pred t) := "(pred " ++ repr t ++ ")"

    instance : has_repr term := ⟨repr⟩

    private def to_string : term → string
    | true := "true"
    | false := "false"
    | (if_then_else t₀ t₁ t₂) :=
        "if " ++ to_string t₀
        ++ " then " ++ to_string t₁
        ++ " else " ++ to_string t₂
    | (iszero t) := "iszero " ++ to_string t
    | zero := "0"
    | (succ t) := "succ " ++ to_string t
    | (pred t) := "pred " ++ to_string t

    instance : has_to_string term := ⟨to_string⟩

    def size : term → ℕ
    | (if_then_else t₀ t₁ t₂) := (size t₀ + size t₁ + size t₂).succ
    | (iszero t₀) := nat.succ $ size t₀
    | (succ t₀) := nat.succ $ size t₀
    | (pred t₀) := nat.succ $ size t₀
    | _ := 1

    def size.pos : ∀(t : term), 0 < t.size
    | (if_then_else t₀ t₁ t₂) := nat.succ_pos (size t₀ + size t₁ + size t₂)
    | (iszero t₀) := nat.succ_pos $ size t₀
    | (succ t₀) := nat.succ_pos $ size t₀
    | (pred t₀) := nat.succ_pos $ size t₀
    | true := nat.succ_pos 0
    | false := nat.succ_pos 0
    | zero := nat.succ_pos 0

  end term

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
      private def const (t : term) : parser term := t <$ symbol (to_string t)
      def true : parser term := const term.true
      def false : parser term := const term.false
      def zero : parser term := const term.zero

      -- Unary
      private def unary
        (symbol_def : string) (mk : term -> term) (inside : parser term)
        : parser term := do
        symbol symbol_def,
        mk <$> inside
      def succ : parser term -> parser term := unary "succ" term.succ
      def pred : parser term -> parser term := unary "pred" term.pred
      def iszero : parser term -> parser term := unary "iszero" term.iszero

      -- if-then-else
      def if_then_else (inside : parser term) : parser term :=
        term.if_then_else
        <$> (symbol "if" *> inside)
        <*> (symbol "then" *> inside)
        <*> (symbol "else" *> inside)

      def term : parser term := parser.fix $ λterm,
         true
        <|> false
        <|> if_then_else term
        <|> zero
        <|> succ term
        <|> pred term
        <|> iszero term
        <|> bracket.paren term

    end term

    def toplevel : parser (list term) :=
      spaces *> parser.many1 (term.term <* semicolon)

  end parser

  namespace eval

    namespace small_step

      inductive eval_relation : term → Type
      | IfTrue (t₁ t₂ : term) : eval_relation (term.if_then_else term.true t₁ t₂)
      | IfFalse (t₁ t₂ : term) : eval_relation (term.if_then_else term.false t₁ t₂) 
      | If (t₀ t₁ t₂ : term) : eval_relation t₀ → eval_relation (term.if_then_else t₀ t₁ t₂)
      | Succ (t₀ : term) : eval_relation t₀ → eval_relation (term.succ t₀)
      | PredZero : eval_relation (term.pred term.zero)
      -- I decided not to reject non-numeric term1inguini
      | PredSucc (t₀ : term) : eval_relation (term.pred (term.succ t₀))
      | Pred (t₀ : term) : eval_relation t₀ → eval_relation (term.pred t₀)
      | IsZeroZero : eval_relation (term.iszero term.zero)
      | IsZeroSucc (t₀ : term) : eval_relation (term.iszero (term.succ t₀))
      | IsZero (t₀ : term) : eval_relation t₀ → eval_relation (term.iszero t₀)

      def maybe_eval_relation : ∀(t : term), option (eval_relation t)
      | (term.if_then_else term.true t₁ t₂) := pure (eval_relation.IfTrue t₁ t₂)
      | (term.if_then_else term.false t₁ t₂) := pure (eval_relation.IfFalse t₁ t₂)
      | (term.if_then_else t₀ t₁ t₂) := do
          e₀ ← maybe_eval_relation t₀,
          pure (eval_relation.If t₀ t₁ t₂ e₀)
      | (term.succ t₀) := do
          e₀ ← maybe_eval_relation t₀,
          pure (eval_relation.Succ t₀ e₀)
      | (term.pred term.zero) := eval_relation.PredZero
      | (term.pred (term.succ t₀)) := pure (eval_relation.PredSucc t₀)
      | (term.pred t₀) := do
          e₀ ← maybe_eval_relation t₀,
          pure (eval_relation.Pred t₀ e₀)
      | (term.iszero term.zero) := pure eval_relation.IsZeroZero
      | (term.iszero (term.succ t₀)) := pure (eval_relation.IsZeroSucc t₀) 
      | (term.iszero t₀) := do
          e₀ ← maybe_eval_relation t₀,
          pure (eval_relation.IsZero t₀ e₀)
      | _ := option.none

      def true_is_normal_form (e : eval_relation term.true) : false := by cases e
      def false_is_normal_form (e : eval_relation term.false) : false := by cases e
      def zero_is_normal_form (e : eval_relation term.zero) : false := by cases e

      -- term may be evaluated or already normal form before evaluation step
      def step : ∀(t : term), eval_relation t → term
      | (term.if_then_else _ _ _) (eval_relation.IfTrue t₁ _) := t₁ 
      | (term.if_then_else _ _ _) (eval_relation.IfFalse _ t₂) := t₂
      | (term.if_then_else _ _ _) (eval_relation.If t₀ t₁ t₂ e₀) :=
          term.if_then_else (step t₀ e₀) t₁ t₂
      | (term.succ _) (eval_relation.Succ t₀ e₀) := term.succ (step t₀ e₀)
      | (term.pred term.zero) eval_relation.PredZero := term.zero
      | (term.pred (term.succ _)) (eval_relation.PredSucc t₀) := t₀
      | (term.pred _) (eval_relation.Pred t₀ e₀) := term.pred (step t₀ e₀)
      | (term.iszero term.zero) eval_relation.IsZeroZero := term.true
      | (term.iszero (term.succ _)) (eval_relation.IsZeroSucc t₀) := term.false 
      | (term.iszero _) (eval_relation.IsZero t₀ e₀) := term.iszero (step t₀ e₀)

      def step_size_decression : ∀(t : term) (e : eval_relation t), (step t e).size < t.size
      | (term.if_then_else term.true _ _) (eval_relation.IfTrue t₁ t₂) :=
          let split : t₁.size + (1 + t₂.size + 1) = 1 + t₁.size + t₂.size + 1 :=
                @id (t₁.size + (1 + t₂.size + 1) = ((1 + t₁.size) + t₂.size) + 1)
                  $ eq.subst (nat.add_comm t₁.size 1)
                
                $ @id (t₁.size + (1 + t₂.size + 1) = ((t₁.size + 1) + t₂.size) + 1)
                  $ eq.subst (nat.add_assoc t₁.size 1 t₂.size).symm
                
                $ @id (t₁.size + (1 + t₂.size + 1) = (t₁.size + (1 + t₂.size)) + 1)
                  $ eq.subst (nat.add_assoc t₁.size (1 + t₂.size) 1)

                $ @id (t₁.size + (1 + t₂.size + 1) = t₁.size + ((1 + t₂.size) + 1))
                  $ rfl
            , zero_lt_sum : 0 < 1 + t₂.size + 1 :=
                nat.zero_lt_succ (1 + t₂.size)
          in @id (t₁.size < (term.if_then_else term.true t₁ t₂).size)
            $ @id (t₁.size < term.true.size + t₁.size + t₂.size + 1)
            $ @id (t₁.size < 1 + t₁.size + t₂.size + 1)
            $ eq.subst split
            $ @id (t₁.size < t₁.size + (1 + t₂.size + 1))
            $ nat.lt_add_of_pos_right zero_lt_sum
      | (term.if_then_else term.false _ _) (eval_relation.IfFalse t₁ t₂) :=
          let split : t₂.size + (1 + t₁.size + 1) = 1 + t₁.size + t₂.size + 1 :=
                @id (t₂.size + (1 + t₁.size + 1) = ((1 + t₁.size) + t₂.size) + 1)
                  $ eq.subst (nat.add_comm t₂.size (1 + t₁.size))

                $ @id (t₂.size + (1 + t₁.size + 1) = (t₂.size + (1 + t₁.size)) + 1)
                  $ eq.subst (nat.add_assoc t₁.size (1 + t₂.size) 1)
                
                $ @id (t₂.size + (1 + t₁.size + 1) = t₂.size + ((1 + t₁.size) + 1))
                  $ rfl
            , zero_lt_sum : 0 < 1 + t₁.size + 1 :=
                nat.zero_lt_succ (1 + t₁.size)
          in @id (t₂.size < (term.if_then_else term.false t₁ t₂).size)
            $ @id (t₂.size < term.false.size + t₁.size + t₂.size + 1)
            $ @id (t₂.size < 1 + t₁.size + t₂.size + 1)
              $ eq.subst split
            $ @id (t₂.size < t₂.size + (1 + t₁.size + 1))
              $ nat.lt_add_of_pos_right zero_lt_sum
      | t@(term.if_then_else _ _ _) e@(eval_relation.If t₀ t₁ t₂ e₀) :=
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((step t e).size < (term.if_then_else t₀ t₁ t₂).size)
            $ @id ((term.if_then_else t₀' t₁ t₂).size < (term.if_then_else t₀ t₁ t₂).size)
            
            $ @id (((t₀'.size + t₁.size) + t₂.size) + 1 < ((t₀.size + t₁.size) + t₂.size) + 1)
              $ eq.subst (nat.add_assoc t₀'.size t₁.size t₂.size).symm
            
            $ @id ((t₀'.size + (t₁.size + t₂.size)) + 1 < ((t₀.size + t₁.size) + t₂.size) + 1)
              $ eq.subst (nat.add_assoc t₀.size t₁.size t₂.size).symm
            
            $ @id ((t₀'.size + (t₁.size + t₂.size)) + 1 < (t₀.size + (t₁.size + t₂.size)) + 1)
              $ eq.subst (nat.add_assoc t₀'.size (t₁.size + t₂.size) 1).symm
            
            $ @id ((t₀'.size + (t₁.size + t₂.size)) + 1 < t₀.size + ((t₁.size + t₂.size) + 1))
              $ eq.subst (nat.add_assoc t₀.size (t₁.size + t₂.size) 1).symm
            
            $ @id (t₀'.size + ((t₁.size + t₂.size) + 1) < t₀.size + ((t₁.size + t₂.size) + 1))
            $ nat.add_lt_add_right smaller ((t₁.size + t₂.size) + 1)
            
      | (term.succ _) (eval_relation.Succ t₀ e₀) :=
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.succ t₀').size < (term.succ t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.pred term.zero) eval_relation.PredZero :=
          @id (term.zero.size < (term.pred term.zero).size)
          $ @id (1 < 2) $ nat.lt.base 1
      | (term.pred (term.succ _)) (eval_relation.PredSucc t₀) :=
          @id (t₀.size < (term.pred (term.succ t₀)).size)
          $ @id (t₀.size < t₀.size + 2)
          $ @id (t₀.size + 0 < t₀.size + 2) $ nat.lt_add_of_pos_right
          $ @id (0 < 2) $ nat.zero_lt_one_add 1
      | (term.pred term.true) (eval_relation.Pred t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.pred t₀').size < (term.pred t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.pred term.false) (eval_relation.Pred t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.pred t₀').size < (term.pred t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.pred (term.if_then_else _ _ _)) (eval_relation.Pred t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.pred t₀').size < (term.pred t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.pred (term.pred _)) (eval_relation.Pred t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.pred t₀').size < (term.pred t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.pred term.zero) (eval_relation.Pred t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.pred t₀').size < (term.pred t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.pred (term.succ _)) (eval_relation.Pred t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.pred t₀').size < (term.pred t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.pred (term.iszero _)) (eval_relation.Pred t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.pred t₀').size < (term.pred t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.iszero term.zero) eval_relation.IsZeroZero :=
          @id (term.true.size < (term.iszero term.zero).size)
          $ @id (1 < 2) $ nat.lt.base 1
      | (term.iszero (term.succ _)) (eval_relation.IsZeroSucc t₀) :=
              @id (term.false.size < (term.iszero (term.succ t₀)).size)
              $ @id (1 < t₀.size + 2) $ nat.succ_lt_succ
              $ @id (0 < t₀.size + 1) $ nat.zero_lt_succ t₀.size
      | (term.iszero term.true) (eval_relation.IsZero t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.iszero t₀').size < (term.iszero t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.iszero term.false) (eval_relation.IsZero t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.iszero t₀').size < (term.iszero t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.iszero (term.if_then_else _ _ _)) (eval_relation.IsZero t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.iszero t₀').size < (term.iszero t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.iszero (term.iszero _)) (eval_relation.IsZero t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.iszero t₀').size < (term.iszero t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.iszero term.zero) (eval_relation.IsZero t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.iszero t₀').size < (term.iszero t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.iszero (term.succ _)) (eval_relation.IsZero t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.iszero t₀').size < (term.iszero t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      | (term.iszero (term.pred _)) (eval_relation.IsZero t₀ e₀) := 
          let t₀' := step t₀ e₀
            , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
          in @id ((term.iszero t₀').size < (term.iszero t₀).size)
            $ @id (t₀'.size + 1 < t₀.size + 1)
            $ nat.succ_lt_succ smaller
      
      private def loop
        : ∀(t : term) (loop : ∀(smaller : term), smaller.size < t.size → term), term
      | t@term.true := λ_, t
      | t@term.false := λ_, t
      | t@term.zero := λ_, t
      | t := λloop,
          match maybe_eval_relation t with
          | option.none := t
          | (option.some (e : eval_relation t)) := loop (step t e) (step_size_decression t e)
          end

      def size_lt_wf : well_founded (λ(t₀ t₁ : term), t₀.size < t₁.size) :=
        inv_image.wf (term.size) nat.lt_wf

      def eval : term → term :=
        well_founded.fix size_lt_wf loop

    end small_step

  end eval

end arith

def main : io unit := do
  test_str ← io.fs.read_file "test.f" ff,
  io.put_str_ln $ match parser.run arith.parser.toplevel test_str with
  | (sum.inl err) := to_string err
  | (sum.inr x) := to_string $ functor.map arith.eval.small_step.eval x
  end

