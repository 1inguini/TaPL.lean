import common

namespace untyped


  -- Type representing term of the language
  inductive term : ℕ → Type
  -- Variable, represented by de Bruijn index
  | var {n : ℕ} (index : fin (nat.succ n)) : term (nat.succ n)
  -- Abstraction, a lambda
  | abs {n : ℕ} (body : term (nat.succ n)) : term n
  -- Function application
  | app {n : ℕ} : term n → term n → term n

  namespace term

    private def repr : ∀{n : ℕ}, term n → string
    | n (term.var index) := let ⟨fin_repr⟩ := fin.has_repr n in "(var " ++ fin_repr index ++ ")"
    | _ (term.abs body) := "(abs " ++ body.repr ++ ")"
    | _ (term.app t₀ t₁) := "(app " ++ t₀.repr ++ " " ++ t₁.repr ++ ")"

    instance {n : ℕ} : has_repr (term n) := ⟨repr⟩

    private def to_string : ∀{n : ℕ}, term n → string
    | n (term.var index) := let ⟨fin_repr⟩ := fin.has_repr n in "#" ++ fin_repr index
    | _ (term.abs body) := "(λ. " ++ to_string body ++ ")"
    | _ (term.app t₀ t₁) := to_string t₀ ++ " " ++ to_string t₁

    instance {n : ℕ} : has_to_string (term n) := ⟨to_string⟩

    def size {n : ℕ} : term n → ℕ

    -- term.size is always positive
    def size.pos {n : ℕ} : ∀(t : term n), 0 < t.size

  end term

  -- Term, before assigning de Bruijn index
  inductive named_term : Type
  | var : string → named_term
  | abs : string → named_term → named_term
  | app : named_term → named_term → named_term

  namespace named_term

    private def repr : named_term → string
    | (named_term.var varname) := "(var " ++ varname ++ ")"
    | (named_term.abs varname body) := "(abs \"" ++ varname  ++ "\" " ++ body.repr ++ ")"
    | (named_term.app t₀ t₁) := "(app " ++ t₀.repr ++ " " ++ t₁.repr ++ ")"

    instance : has_repr named_term := ⟨repr⟩

    private def to_string : named_term → string
    | (named_term.var varname) := varname
    | (named_term.abs varname body) := "λ" ++ varname ++ ". " ++ to_string body
    | (named_term.app t₀ t₁) := "(" ++ to_string t₀ ++ ") (" ++ to_string t₁ ++ ")"

  end named_term

  namespace parser

    private def var : parser named_term := named_term.var <$> parser.identifier
    private def abs (term : parser named_term) : parser named_term := do
      parser.word.lambda,
      v ← parser.identifier,
      parser.dot,
      named_term.abs v <$> term
    private def app (term : parser named_term) : parser named_term :=
      named_term.app <$> term <*> term

    -- Parser for the language, before assigning de Bruijn index
    private def named_term_toplevel : parser (list named_term) := parser.terms $ λterm,
      abs term
      <|> app term
      <|> var
      <|> parser.bracket.paren term

  end parser

  namespace naming
  
    -- Naming context
    def naming_context (n : ℕ) : Type := array n string

    -- Search array from the end
    private def rev_find {α : Type} (p : α → Prop) [decidable_pred p] {n : ℕ} (a : array n.succ α)
      : option (fin n.succ) :=
      a.rev_iterate option.none $ λi x acc,
        match acc with
        | option.none := do guard $ p x, pure $ 0 - 1 - i
        | result := result
        end

    private def removenames_internal
      : ∀{n : ℕ}, named_term → reader (naming_context n) (option $ term n)
    | (nat.succ _) (named_term.var varname) := do
        ctx ← read,
        pure $ do
          index ← rev_find (eq varname) ctx,
          pure $ term.var $ index
    | 0 (named_term.var _) := pure option.none
    | _ (named_term.abs varname body) := do
        ctx ← read,
        pure $ functor.map term.abs $
          (removenames_internal body).run $ ctx.push_back varname
    | _ (named_term.app i₀ i₁) := do
          t₀ ← removenames_internal i₀,
          t₁ ← removenames_internal i₁,
          pure $ term.app <$> t₀ <*> t₁

    -- Convert named_term to term with givin naming context
    def removenames {n : ℕ} (ctx : naming_context n) (i : named_term) : option (term n) :=
      (removenames_internal i).run ctx

  end naming

  namespace small_step

    -- Evaluation relations as a Type
    inductive eval_relation : term → Type
    | IfTrue (t₁ t₂ : term) : eval_relation (term.if_then_else term.true t₁ t₂)
    | IfFalse (t₁ t₂ : term) : eval_relation (term.if_then_else term.false t₁ t₂)
    | If (t₀ t₁ t₂ : term) : eval_relation t₀ → eval_relation (term.if_then_else t₀ t₁ t₂)
    | Succ (t₀ : term) : eval_relation t₀ → eval_relation (term.succ t₀)
    | PredZero : eval_relation (term.pred term.zero)
    -- I decided not to reject non-numeric term
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

  end small_step

  -- Read, Evaluate, Print
  def main (src : char_buffer) : io unit := do
    match parser.run parser.toplevel src with
    | (sum.inl err) := io.print_ln err
    | (sum.inr ts) := io.print_ln $
        functor.map small_step.eval ts
    end

end untyped