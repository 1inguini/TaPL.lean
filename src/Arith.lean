-- import common

namespace Arith

  -- Type representing term of the language
  inductive Term : Type
  | true : Term
  | false : Term
  | ifThenElse : Term → Term → Term → Term
  | iszero : Term → Term
  | zero : Term
  | succ : Term → Term
  | pred : Term → Term
  deriving DecidableEq, Repr

  namespace Term 

    private def toString : Term → String
    | true => "true"
    | false => "false"
    | (ifThenElse t₀ t₁ t₂) =>
        "if " ++ toString t₀
        ++ " then " ++ toString t₁
        ++ " else " ++ toString t₂
    | (iszero t) => "iszero " ++ toString t
    | zero => "0"
    | (succ t) => "succ " ++ toString t
    | (pred t) => "pred " ++ toString t

    instance : ToString Term := ⟨toString⟩

    def size : Term → Nat
    | (ifThenElse t₀ t₁ t₂) => (size t₀ + size t₁ + size t₂).succ
    | (iszero t₀) => Nat.succ <| size t₀
    | (succ t₀) => Nat.succ <| size t₀
    | (pred t₀) => Nat.succ <| size t₀
    | _ => 1

    -- Term.size is always positive
    def size.pos : ∀(t : Term), 0 < t.size
    | (ifThenElse t₀ t₁ t₂) => Nat.succ_pos (size t₀ + size t₁ + size t₂)
    | (iszero t₀) => Nat.succ_pos <| size t₀
    | (succ t₀) => Nat.succ_pos <| size t₀
    | (pred t₀) => Nat.succ_pos <| size t₀
    | true => Nat.succ_pos 0
    | false => Nat.succ_pos 0
    | zero => Nat.succ_pos 0

  end Term

--   namespace parser

--     -- Constant
--     def true : parser term := term.true <$ parser.word.true
--     def false : parser term := term.false <$ parser.word.false
--     def zero : parser term := term.zero <$ parser.symbol "0"

--     -- Unary
--     private def unary
--       (symbol : parser unit) (mk : term -> term) (inside : parser term)
--       : parser term :=
--       mk <$> (symbol *> inside)
--     def succ : parser term -> parser term := unary parser.word.succ term.succ
--     def pred : parser term -> parser term := unary parser.word.pred term.pred
--     def iszero : parser term -> parser term := unary parser.word.iszero term.iszero

--     -- if-then-else
--     def ifThenElse (inside : parser term) : parser term :=
--       term.ifThenElse
--       <$> (parser.word.if *> inside)
--       <*> (parser.word.then *> inside)
--       <*> (parser.word.else *> inside)

--     -- Parser for the language
--     def toplevel : parser (list term) := parser.terms $ λterm,
--       true
--       <|> false
--       <|> ifThenElse term
--       <|> zero
--       <|> succ term
--       <|> pred term
--       <|> iszero term
--       <|> parser.bracket.paren term

--   end parser

--   namespace small_step

--     -- Evaluation relations as a Type
--     inductive eval_relation : term → Type
--     | IfTrue (t₁ t₂ : term) : eval_relation (term.ifThenElse term.true t₁ t₂)
--     | IfFalse (t₁ t₂ : term) : eval_relation (term.ifThenElse term.false t₁ t₂) 
--     | If (t₀ t₁ t₂ : term) : eval_relation t₀ → eval_relation (term.ifThenElse t₀ t₁ t₂)
--     | Succ (t₀ : term) : eval_relation t₀ → eval_relation (term.succ t₀)
--     | PredZero : eval_relation (term.pred term.zero)
--     -- I decided not to reject non-numeric term
--     | PredSucc (t₀ : term) : eval_relation (term.pred (term.succ t₀))
--     | Pred (t₀ : term) : eval_relation t₀ → eval_relation (term.pred t₀)
--     | IsZeroZero : eval_relation (term.iszero term.zero)
--     | IsZeroSucc (t₀ : term) : eval_relation (term.iszero (term.succ t₀))
--     | IsZero (t₀ : term) : eval_relation t₀ → eval_relation (term.iszero t₀)

--     -- Deduce a evaluation relation from a term
--     def maybe_eval_relation : ∀(t : term), option (eval_relation t)
--     | (term.ifThenElse term.true t₁ t₂) := pure (eval_relation.IfTrue t₁ t₂)
--     | (term.ifThenElse term.false t₁ t₂) := pure (eval_relation.IfFalse t₁ t₂)
--     | (term.ifThenElse t₀ t₁ t₂) := do
--         e₀ ← maybe_eval_relation t₀,
--         pure (eval_relation.If t₀ t₁ t₂ e₀)
--     | (term.succ t₀) := do
--         e₀ ← maybe_eval_relation t₀,
--         pure (eval_relation.Succ t₀ e₀)
--     | (term.pred term.zero) := eval_relation.PredZero
--     | (term.pred (term.succ t₀)) := pure (eval_relation.PredSucc t₀)
--     | (term.pred t₀) := do
--         e₀ ← maybe_eval_relation t₀,
--         pure (eval_relation.Pred t₀ e₀)
--     | (term.iszero term.zero) := pure eval_relation.IsZeroZero
--     | (term.iszero (term.succ t₀)) := pure (eval_relation.IsZeroSucc t₀) 
--     | (term.iszero t₀) := do
--         e₀ ← maybe_eval_relation t₀,
--         pure (eval_relation.IsZero t₀ e₀)
--     | _ := option.none

--     def true_is_normal_form (e : eval_relation term.true) : false := by cases e
--     def false_is_normal_form (e : eval_relation term.false) : false := by cases e
--     def zero_is_normal_form (e : eval_relation term.zero) : false := by cases e

--     -- Evaluate term with corresponding evaluation relation
--     def step : ∀(t : term), eval_relation t → term
--     | (term.ifThenElse _ _ _) (eval_relation.IfTrue t₁ _) := t₁ 
--     | (term.ifThenElse _ _ _) (eval_relation.IfFalse _ t₂) := t₂
--     | (term.ifThenElse _ _ _) (eval_relation.If t₀ t₁ t₂ e₀) :=
--         term.ifThenElse (step t₀ e₀) t₁ t₂
--     | (term.succ _) (eval_relation.Succ t₀ e₀) := term.succ (step t₀ e₀)
--     | (term.pred term.zero) eval_relation.PredZero := term.zero
--     | (term.pred (term.succ _)) (eval_relation.PredSucc t₀) := t₀
--     | (term.pred _) (eval_relation.Pred t₀ e₀) := term.pred (step t₀ e₀)
--     | (term.iszero term.zero) eval_relation.IsZeroZero := term.true
--     | (term.iszero (term.succ _)) (eval_relation.IsZeroSucc t₀) := term.false 
--     | (term.iszero _) (eval_relation.IsZero t₀ e₀) := term.iszero (step t₀ e₀)

--     -- A proof that term.size of the term decreases after step is applied to it
--     -- Lots of obvious pattern matches are needed
--     def step_size_decression : ∀(t : term) (e : eval_relation t), (step t e).size < t.size
--     | (term.ifThenElse term.true _ _) (eval_relation.IfTrue t₁ t₂) :=
--         let split : t₁.size + (1 + t₂.size + 1) = 1 + t₁.size + t₂.size + 1 :=
--               @id (t₁.size + (1 + t₂.size + 1) = ((1 + t₁.size) + t₂.size) + 1)
--                 $ eq.subst (nat.add_comm t₁.size 1)
              
--               $ @id (t₁.size + (1 + t₂.size + 1) = ((t₁.size + 1) + t₂.size) + 1)
--                 $ eq.subst (nat.add_assoc t₁.size 1 t₂.size).symm
              
--               $ @id (t₁.size + (1 + t₂.size + 1) = (t₁.size + (1 + t₂.size)) + 1)
--                 $ eq.subst (nat.add_assoc t₁.size (1 + t₂.size) 1)

--               $ @id (t₁.size + (1 + t₂.size + 1) = t₁.size + ((1 + t₂.size) + 1))
--                 $ rfl
--           , zero_lt_sum : 0 < 1 + t₂.size + 1 :=
--               nat.zero_lt_succ (1 + t₂.size)
--         in @id (t₁.size < (term.ifThenElse term.true t₁ t₂).size)
--           $ @id (t₁.size < term.true.size + t₁.size + t₂.size + 1)
--           $ @id (t₁.size < 1 + t₁.size + t₂.size + 1)
--           $ eq.subst split
--           $ @id (t₁.size < t₁.size + (1 + t₂.size + 1))
--           $ nat.lt_add_of_pos_right zero_lt_sum
--     | (term.ifThenElse term.false _ _) (eval_relation.IfFalse t₁ t₂) :=
--         let split : t₂.size + (1 + t₁.size + 1) = 1 + t₁.size + t₂.size + 1 :=
--               @id (t₂.size + (1 + t₁.size + 1) = ((1 + t₁.size) + t₂.size) + 1)
--                 $ eq.subst (nat.add_comm t₂.size (1 + t₁.size))

--               $ @id (t₂.size + (1 + t₁.size + 1) = (t₂.size + (1 + t₁.size)) + 1)
--                 $ eq.subst (nat.add_assoc t₁.size (1 + t₂.size) 1)
              
--               $ @id (t₂.size + (1 + t₁.size + 1) = t₂.size + ((1 + t₁.size) + 1))
--                 $ rfl
--           , zero_lt_sum : 0 < 1 + t₁.size + 1 :=
--               nat.zero_lt_succ (1 + t₁.size)
--         in @id (t₂.size < (term.ifThenElse term.false t₁ t₂).size)
--           $ @id (t₂.size < term.false.size + t₁.size + t₂.size + 1)
--           $ @id (t₂.size < 1 + t₁.size + t₂.size + 1)
--             $ eq.subst split
--           $ @id (t₂.size < t₂.size + (1 + t₁.size + 1))
--             $ nat.lt_add_of_pos_right zero_lt_sum
--     | t@(term.ifThenElse _ _ _) e@(eval_relation.If t₀ t₁ t₂ e₀) :=
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((step t e).size < (term.ifThenElse t₀ t₁ t₂).size)
--           $ @id ((term.ifThenElse t₀' t₁ t₂).size < (term.ifThenElse t₀ t₁ t₂).size)
          
--           $ @id (((t₀'.size + t₁.size) + t₂.size) + 1 < ((t₀.size + t₁.size) + t₂.size) + 1)
--             $ eq.subst (nat.add_assoc t₀'.size t₁.size t₂.size).symm
          
--           $ @id ((t₀'.size + (t₁.size + t₂.size)) + 1 < ((t₀.size + t₁.size) + t₂.size) + 1)
--             $ eq.subst (nat.add_assoc t₀.size t₁.size t₂.size).symm
          
--           $ @id ((t₀'.size + (t₁.size + t₂.size)) + 1 < (t₀.size + (t₁.size + t₂.size)) + 1)
--             $ eq.subst (nat.add_assoc t₀'.size (t₁.size + t₂.size) 1).symm
          
--           $ @id ((t₀'.size + (t₁.size + t₂.size)) + 1 < t₀.size + ((t₁.size + t₂.size) + 1))
--             $ eq.subst (nat.add_assoc t₀.size (t₁.size + t₂.size) 1).symm
          
--           $ @id (t₀'.size + ((t₁.size + t₂.size) + 1) < t₀.size + ((t₁.size + t₂.size) + 1))
--           $ nat.add_lt_add_right smaller ((t₁.size + t₂.size) + 1)
          
--     | (term.succ _) (eval_relation.Succ t₀ e₀) :=
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.succ t₀').size < (term.succ t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.pred term.zero) eval_relation.PredZero :=
--         @id (term.zero.size < (term.pred term.zero).size)
--         $ @id (1 < 2) $ nat.lt.base 1
--     | (term.pred (term.succ _)) (eval_relation.PredSucc t₀) :=
--         @id (t₀.size < (term.pred (term.succ t₀)).size)
--         $ @id (t₀.size < t₀.size + 2)
--         $ @id (t₀.size + 0 < t₀.size + 2) $ nat.lt_add_of_pos_right
--         $ @id (0 < 2) $ nat.zero_lt_one_add 1
--     | (term.pred term.true) (eval_relation.Pred t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.pred t₀').size < (term.pred t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.pred term.false) (eval_relation.Pred t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.pred t₀').size < (term.pred t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.pred (term.ifThenElse _ _ _)) (eval_relation.Pred t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.pred t₀').size < (term.pred t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.pred (term.pred _)) (eval_relation.Pred t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.pred t₀').size < (term.pred t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.pred term.zero) (eval_relation.Pred t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.pred t₀').size < (term.pred t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.pred (term.succ _)) (eval_relation.Pred t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.pred t₀').size < (term.pred t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.pred (term.iszero _)) (eval_relation.Pred t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.pred t₀').size < (term.pred t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.iszero term.zero) eval_relation.IsZeroZero :=
--         @id (term.true.size < (term.iszero term.zero).size)
--         $ @id (1 < 2) $ nat.lt.base 1
--     | (term.iszero (term.succ _)) (eval_relation.IsZeroSucc t₀) :=
--             @id (term.false.size < (term.iszero (term.succ t₀)).size)
--             $ @id (1 < t₀.size + 2) $ nat.succ_lt_succ
--             $ @id (0 < t₀.size + 1) $ nat.zero_lt_succ t₀.size
--     | (term.iszero term.true) (eval_relation.IsZero t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.iszero t₀').size < (term.iszero t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.iszero term.false) (eval_relation.IsZero t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.iszero t₀').size < (term.iszero t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.iszero (term.ifThenElse _ _ _)) (eval_relation.IsZero t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.iszero t₀').size < (term.iszero t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.iszero (term.iszero _)) (eval_relation.IsZero t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.iszero t₀').size < (term.iszero t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.iszero term.zero) (eval_relation.IsZero t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.iszero t₀').size < (term.iszero t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.iszero (term.succ _)) (eval_relation.IsZero t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.iszero t₀').size < (term.iszero t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
--     | (term.iszero (term.pred _)) (eval_relation.IsZero t₀ e₀) := 
--         let t₀' := step t₀ e₀
--           , smaller : t₀'.size < t₀.size := step_size_decression t₀ e₀
--         in @id ((term.iszero t₀').size < (term.iszero t₀).size)
--           $ @id (t₀'.size + 1 < t₀.size + 1)
--           $ nat.succ_lt_succ smaller
    
--     -- Function to be passed to well_founded.fix
--     private def loop
--       : ∀(t : term) (loop : ∀(smaller : term), smaller.size < t.size → term), term
--     | t@term.true := λ_, t
--     | t@term.false := λ_, t
--     | t@term.zero := λ_, t
--     | t := λloop,
--         match maybe_eval_relation t with
--         | option.none := t
--         | (option.some (e : eval_relation t)) := loop (step t e) (step_size_decression t e)
--         end

--     -- Proof to be passed to well_founded.fix
--     def size_lt_wf : well_founded (λ(t₀ t₁ : term), t₀.size < t₁.size) :=
--       inv_image.wf (term.size) nat.lt_wf

--     def eval : term → term :=
--       well_founded.fix size_lt_wf loop

--   end small_step

--   -- Read, Evaluate, Print
--   def main (src : char_buffer) : io unit := do
--     match parser.run parser.toplevel src with
--     | (sum.inl err) := io.print_ln err
--     | (sum.inr ts) := io.print_ln $
--         functor.map small_step.eval ts
--     end

end Arith