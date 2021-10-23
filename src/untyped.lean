import common

namespace untyped


  -- Type representing term of the language
  inductive term : ℕ → Type
  -- Variable, represented by de Bruijn index
  | var {n : ℕ} (index : fin (n + 1)) : term (n + 1)
  -- Abstraction, a lambda
  | abs {n : ℕ} (body : term (n + 1)) : term n
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

    def size {n : ℕ} : term n → ℕ := sorry

    -- term.size is always positive
    def size.pos {n : ℕ} : ∀(t : term n), 0 < t.size := sorry

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

  namespace naming
  
    -- Naming context
    def naming_context (n : ℕ) : Type := array n string

    -- Search array from the end
    private def rev_find {α : Type} (p : α → Prop) [decidable_pred p] {n : ℕ} (a : array (n + 1) α)
      : option (fin (n + 1)) :=
      a.rev_iterate option.none $ λi x acc,
        match acc with
        | option.none := do guard $ p x, pure $ 0 - 1 - i
        | result := result
        end

    -- Convert named_term to term with givin naming context
    def removenames
      : ∀{n : ℕ}, named_term → reader (naming_context n) (option $ term n)
    | (_ + 1) (named_term.var varname) := do
        Γ ← read,
        pure $ do
          index ← rev_find (eq varname) Γ,
          pure $ term.var $ index
    | 0 (named_term.var _) := pure option.none
    | _ (named_term.abs varname body) := do
        Γ ← read,
        pure $ functor.map term.abs $
          (removenames body).run $ Γ.push_back varname
    | _ (named_term.app nt₀ nt₁) := do
          t₀ ← removenames nt₀,
          t₁ ← removenames nt₁,
          pure $ term.app <$> t₀ <*> t₁

  end naming

  namespace parser

    private def var : parser named_term := named_term.var <$> parser.identifier
    private def abs (term : parser named_term) : parser named_term := do
      parser.word.lambda,
      v ← parser.identifier,
      parser.dot,
      named_term.abs v <$> term
    private def app (term : parser named_term) : parser named_term := parser.fix $ λapp, do
      t :: ts ← parser.many1 $ abs app <|> var,
      pure $ list.foldl (named_term.app) t ts

    private def term : parser named_term := app $ abs

    -- Parser for the language, before assigning de Bruijn index
    def named_term_toplevel : parser (list named_term) := parser.terms $ λterm,
      parser.bracket.paren term
      <|> app term
      -- <|> parser.decorate_error "Application" (app term)
      -- <|> parser.decorate_error "Abstraction" (abs term)
      -- <|> parser.decorate_error "Variable" var

    def toplevel : parser (list (option $ term 0)) := do
      nts ← named_term_toplevel,
      pure $ (λnt, (naming.removenames nt).run array.nil) <$> nts

  end parser

  def shift_succ : ∀{n : ℕ}, fin n → term n → term (n + 1)
  | _ c t@(term.var k) := term.var (if k < c then ⟨k.val, k.property.step⟩ else k.succ)
  | _ c (term.abs t₀) := term.abs $ shift_succ c.succ t₀
  | _ c (term.app t₀ t₁) := term.app (shift_succ c t₀) (shift_succ c t₀)

  -- def shift_pred : ∀{n : ℕ} (c : fin (n + 1)), term (n + 1) → term n
  -- | n c (term.var k) := term.var $
  --     if pk : k ≠ 0 then k.pred pk + (if k < c then 1 else 0)
  --     else 0
  -- | _ c (term.abs t₀) := term.abs $ shift_pred c.succ t₀
  -- | _ c (term.app t₀ t₁) := term.app (shift_pred c t₀) (shift_pred c t₀)
  
  def β_reduction₀ : term 0 → term 1 → term 0
  | s t@(term.var k) := if j = k then s else t
  | s t@(term.abs body) := term.abs $ β_reduction j.succ (shift_succ 0 s) body
  | s (term.app t₀ t₁) := term.app (β_reduction j s t₀) (β_reduction j s t₁)
  
  namespace small_step

    -- Evaluation relations as a Type
    inductive eval_relation : ∀{n : ℕ}, term n → Type
    | App1 {n : ℕ} {t₀ t₁ : term n}
      : eval_relation t₀ → eval_relation (term.app t₀ t₁)
    | App2 {n : ℕ} {body₀ : term (n + 1)} {t₁ : term n} 
      : eval_relation t₁ → eval_relation (term.app (term.abs body₀) t₁)
    | AppAbs {n : ℕ} {body₀ body₁ : term (n + 1)}
      : eval_relation (term.app (term.abs body₀) (term.abs body₁))

    -- Deduce a evaluation relation from a term
    def mk_eval_relation : ∀(t : term 0), option $ eval_relation t
    | (term.app t₀@(term.app _ _) t₁) := eval_relation.App1 <$> mk_eval_relation t₀
    | (term.app (term.abs _) t@(term.app _ _)) := eval_relation.App2 <$> mk_eval_relation t
    | (term.app (term.abs _) (term.abs _)) := pure eval_relation.AppAbs
    | (term.abs _) := option.none

    -- Evaluate term with corresponding evaluation relation
    def step : ∀(t : term 0), eval_relation t → term 0
    | (term.app t₀ t₁) (eval_relation.App1 tr₀) := term.app (step t₀ tr₀) t₁
    | (term.app v₀ t₁) (eval_relation.App2 tr₁) := term.app v₀ (step t₁ tr₁)
    | (term.app (term.abs body₀) v₁) (eval_relation.AppAbs) :=
      β_reduction₀ (shift_succ 0 v₁) body₀

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
        /- functor.map small_step.eval -/ ts
    end

end untyped