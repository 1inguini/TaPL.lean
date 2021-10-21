import common

namespace tyarith

  -- Type representing term of the language
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

    -- term.size is always positive
    def size.pos : ∀(t : term), 0 < t.size
    | (if_then_else t₀ t₁ t₂) := nat.succ_pos (size t₀ + size t₁ + size t₂)
    | (iszero t₀) := nat.succ_pos $ size t₀
    | (succ t₀) := nat.succ_pos $ size t₀
    | (pred t₀) := nat.succ_pos $ size t₀
    | true := nat.succ_pos 0
    | false := nat.succ_pos 0
    | zero := nat.succ_pos 0

  end term

  -- Type representing type of the language
  @[derive decidable_eq]
  inductive type : Type
  | Nat : type
  | Bool : type

  namespace type

    instance : has_repr type := ⟨λt, match t with
      | type.Nat := "Nat"
      | type.Bool := "Bool"
      end⟩

    instance : has_to_string type := ⟨repr⟩

  end type

  namespace parser

    -- Constant
    def true : parser term := term.true <$ parser.word.true
    def false : parser term := term.false <$ parser.word.false
    def zero : parser term := term.zero <$ parser.symbol "0"

    -- Unary
    private def unary
      (symbol : parser unit) (mk : term -> term) (inside : parser term)
      : parser term :=
      mk <$> (symbol *> inside)
    def succ : parser term -> parser term := unary parser.word.succ term.succ
    def pred : parser term -> parser term := unary parser.word.pred term.pred
    def iszero : parser term -> parser term := unary parser.word.iszero term.iszero

    -- if-then-else
    def if_then_else (inside : parser term) : parser term :=
      term.if_then_else
      <$> (parser.word.if *> inside)
      <*> (parser.word.then *> inside)
      <*> (parser.word.else *> inside)

    -- Parser for the language
    def toplevel : parser (list term) := parser.terms $ λterm,
      true
      <|> false
      <|> if_then_else term
      <|> zero
      <|> succ term
      <|> pred term
      <|> iszero term
      <|> parser.bracket.paren term

  end parser

  namespace small_step

    -- Evaluation relations as a Type
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

    -- Deduce a evaluation relation from a term
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

    -- Evaluate term with corresponding evaluation relation
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

    -- A proof that term.size of the term decreases after step is applied to it
    -- Lots of obvious pattern matches are needed
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
    
    -- Function to be passed to well_founded.fix
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

    -- Proof to be passed to well_founded.fix
    def size_lt_wf : well_founded (λ(t₀ t₁ : term), t₀.size < t₁.size) :=
      inv_image.wf (term.size) nat.lt_wf

    def eval : term → term :=
      well_founded.fix size_lt_wf loop

  -- Typing relations as a Type
  inductive type_relation : type → term → Type
    | True : type_relation type.Bool term.true
    | False : type_relation type.Bool term.false
    | If {T₁ T₂ : type} {t₀ t₁ t₂ : term}
      : type_relation type.Bool t₀
      → T₁ = T₂
      → type_relation T₁ t₁
      → type_relation T₂ t₂
      → type_relation T₁ (term.if_then_else t₀ t₁ t₂)
    | Zero : type_relation type.Nat term.zero
    | Succ {t₀ : term} : type_relation type.Nat t₀ → type_relation type.Nat (term.succ t₀)
    | Pred {t₀ : term} : type_relation type.Nat t₀ → type_relation type.Nat (term.pred t₀)
    | IsZero {t₀ : term} : type_relation type.Nat t₀ → type_relation type.Bool (term.iszero t₀)

    -- Deduce a type and typing relation from a term
    def maybe_type_relation : ∀(t : term), option Σ(T : type), type_relation T t
    | term.true := pure ⟨type.Bool, type_relation.True⟩
    | term.false := pure ⟨type.Bool, type_relation.False⟩
    | (term.if_then_else t₀ t₁ t₂) := do
        Ttr₀ <- maybe_type_relation t₀,
        match Ttr₀ with
        | ⟨type.Bool, tr₀⟩ := do
            ⟨T₁, tr₁⟩ <- maybe_type_relation t₁,
            ⟨T₂, tr₂⟩ <- maybe_type_relation t₂,
            if ok : T₁ = T₂
            then pure ⟨T₁, type_relation.If tr₀ ok tr₁ tr₂⟩
            else option.none
        | _ := option.none
        end
    | term.zero := pure ⟨type.Nat, type_relation.Zero⟩
    | (term.succ t₀) := do
        Ttr₀ <- maybe_type_relation t₀,
        match Ttr₀ with
        | ⟨type.Nat, tr₀⟩ := pure ⟨type.Nat, type_relation.Succ tr₀⟩
        | _ := option.none
        end
    | (term.pred t₀) := do
        Ttr₀ <- maybe_type_relation t₀,
        match Ttr₀ with
        | ⟨type.Nat, tr₀⟩ := pure ⟨type.Nat, type_relation.Pred tr₀⟩
        | _ := option.none
        end
    | (term.iszero t₀) := do
        Ttr₀ <- maybe_type_relation t₀,
        match Ttr₀ with
        | ⟨type.Nat, tr₀⟩ := pure ⟨type.Bool, type_relation.IsZero tr₀⟩
        | _ := option.none
        end

      def typecheck (t : term) : option type :=
        match maybe_type_relation t with
        | option.none := option.none
        | option.some ⟨T, _⟩ := T
        end

  end small_step

  -- Read, Evaluate, Print
  def main (src : char_buffer) : io unit := do
    match parser.run parser.toplevel src with
    | (sum.inl err) := io.put_str_ln err
    | (sum.inr ts) := io.print_ln $
        functor.map (λt, (small_step.typecheck t, small_step.eval t)) ts
    end

end tyarith