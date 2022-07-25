-- Common functions shared across languages, such as parser for keywords

import Std.Data.HashMap
open Std

-- def HashSet.singleton {α : Type u} [BEq α] [Hashable α] (a : α) :=
--   HashSet.insert HashSet.empty a

def rw (motive : α → Prop) : a = b → motive a → motive b := @Eq.subst _ motive _ _

-- https://matt.might.net/papers/might2011derivatives.pdf
namespace Parser

  private def Fin.max : Fin (Nat.succ k) := 0 - 1
  private def Fin.ext : Fin k → Fin (k.succ)
    | ⟨n, h⟩ => ⟨n, Nat.le_succ_of_le h⟩

  def Index (ls : List α) : Type := Fin ls.length
  def Index.last : Index (l :: ls) := Fin.max
  def Index.zero : Index (l :: ls) := ⟨0, Nat.le_add_left 1 ls.length⟩

  def isLt (xs ys : List α) {index : Index xs} : ys.length + index.val < (ys ++ xs).length :=
    let goal : index.val < xs.length := index.isLt
    let goal : ys.length + index.val.succ ≤ ys.length + xs.length :=
      Nat.add_le_add_left goal ys.length
    let goal : (ys.length + index.val).succ ≤ ys.length + xs.length :=
      rw (. ≤ ys.length + xs.length) (Nat.add_succ ys.length index.val) goal
    let goal : ys.length + index.val < ys.length + xs.length := Nat.lt_of_succ_le goal
    let goal : ys.length + index.val < (ys ++ xs).length :=
      rw (ys.length + index.val < .) (List.length_append ys xs).symm goal
    goal

  def dropUntilIndex : (xs : List α) → Index xs → List α
    | _ :: xs, ⟨0, _⟩ => xs
    | _ :: xs, ⟨Nat.succ k, h⟩ => dropUntilIndex xs ⟨k, Nat.le_of_succ_le_succ h⟩

  def dropWithIndex_zero : {xs : List α} →
    dropUntilIndex (x :: xs) ⟨0, Nat.le_add_left 1 xs.length⟩ = xs
    | [] => rfl
    | _ :: _ => rfl

  def length_dropWithIndex :
    {xs : List α} → {i : Index xs} →
    (dropUntilIndex xs i).length + i.val + 1 = xs.length
    | x :: xs, ⟨0 , h⟩ =>
      let zero : Index (x :: xs) := ⟨0, h⟩
      let goal := Eq.refl <| (dropUntilIndex (x :: xs) zero).length + 1
      let goal : (dropUntilIndex (x :: xs) zero).length + 1 = xs.length + 1 := goal
      let goal : (dropUntilIndex (x :: xs) zero).length + zero.val + 1 = (x :: xs).length := goal
      goal
    | x :: xs, ⟨Nat.succ k, h⟩ =>
      let i : Index (x :: xs) := ⟨Nat.succ k, h⟩
      let iPrev : Index xs := ⟨k, Nat.le_of_succ_le_succ h⟩
      let prev : (dropUntilIndex xs iPrev).length + iPrev.val + 1 = xs.length := length_dropWithIndex
      let lhs := (dropUntilIndex (x :: xs) i).length + i.val + 1
      let goal := Eq.refl lhs
      let goal : lhs = (dropUntilIndex xs iPrev).length + i.val + 1 := goal
      let goal : lhs = (dropUntilIndex xs iPrev).length + iPrev.val + 1 + 1 := goal
      let goal : lhs = xs.length + 1 := rw (lhs = . + 1) prev goal
      let goal : lhs = (x :: xs).length := goal
      goal

  def length_map {α β : Type u} (f : α → β) : (xs : List α) → xs.length = (List.map f xs).length
    | [] => rfl
    | x :: xs =>
      let lhs : xs.length.succ = (x :: xs).length := List.length_cons x xs
      let rhs : xs.length.succ = (List.map f (x :: xs)).length :=
        let goal : (List.map f xs).length.succ = (f x :: List.map f xs).length :=
          List.length_cons (f x) (List.map f xs)
        let goal : (List.map f xs).length.succ = (List.map f (x :: xs)).length := goal
        let goal : xs.length.succ = (List.map f (x :: xs)).length :=
          rw (Nat.succ . = (List.map f (x :: xs)).length) (length_map f xs).symm goal
        goal
      let goal : (x :: xs).length = (List.map f (x :: xs)).length :=
        rfl |>
          rw (. = xs.length.succ) lhs |>
          rw ((x :: xs).length = .) rhs
      goal

  private theorem List.cons_get_eq (x : α) (xs : List α) (i : Index xs)
    : (x :: xs).get i.succ = xs.get i := rfl

  -- def autoShift {C : List Type → Type 1} :
  --   {αs : List Type} → (proxy : C βs) →
  --   {sublist : βs = γs ++ αs} →
  --   Ref αs α → Ref βs α
  --   | [], ref => ref
  --   | β :: αs, ref =>
  --     -- let n : Index αs := ⟨k.succ, isLt⟩
  --     -- let indexLastRemoved : Index αs := ⟨k, Nat.le_of_succ_le_succ isLt⟩
  --     -- let nPred : Fin αs.length.succ := ⟨k, Nat.le_of_succ_le isLt⟩
  --     let prev : ({n : Index (β :: αs)} → Ref (dropUntilIndex (β :: αs) n) α) → Ref (β :: αs) α :=
  --       autoShift proxy
  --     let goal {n : Index (β :: αs)} : Ref (dropUntilIndex (β :: αs) n) α := ref
  --     let goal {n : Index (β :: αs)} : Ref ((β :: αs).get n :: dropUntilIndex (β :: αs) n) α :=
  --       ref.shift
  --     let goal {n : Index (β :: αs)} : Ref (dropUntilIndex (β :: αs) n) α := prev goal
  --     goal

  -- inductive Ref : List Nat → Type → Type 1 where
  --   | mk (indexFromLast : Nat) : Ref depends α

  -- structure Ref (α : Type) where
  --   size : Nat
  --   index : Fin size
  --   isValid : {C : Type → Type 1} → (ls : List <| (α : Type) ×' (C α : Type 1)) → (ok : size = ls.length) →
  --     (ls.get (⟨size - index.val, Nat.sub_le size index.val⟩)).fst = α
  namespace Ref

    -- def index (_ : Ref (new ++ α :: old) α) : Nat := new.length

    -- def resize {size tailSize : Nat} (_ : Ref size α) : Ref (size + tailSize) α := Ref.mk

  end Ref
    -- index : Fin size

  -- def Ref.expand (ref : Ref α) (ok : ref.size ≤ newSize) : Ref α := {
  --       size := newSize
  --       index := ⟨newSize - ref.size + ref.index.val,
  --         let goal : newSize ≤ newSize := Nat.le_refl newSize
  --         let goal : newSize - ref.size + ref.size ≤ newSize :=
  --           rw (. ≤ newSize) (Nat.sub_add_cancel ok).symm goal
  --         let goal : newSize - ref.size + ref.index.val < newSize :=
  --           let subGoal : newSize - ref.size + ref.index.val < newSize - ref.size + ref.size :=
  --             Nat.add_le_add_left ref.index.isLt (newSize - ref.size)
  --           Nat.le_trans subGoal goal
  --         goal
  --       ⟩
  --     }

  -- inductive Refs : Type 1 where
  --   | zero : Refs
  --   | one {α : Type} {size : Nat} : Ref size α → Refs
  --   | same {α : Type} {αSize βSize : Nat} : Ref βSize α → Ref αSize α → Refs
  --   | two {α β : Type} {αSize βSize : Nat} : Ref αSize α → Ref βSize β → Refs

  mutual

    inductive Parser : {parser : List Type} → Type → Type 1 where
    -- private inductive Parser : Refs → Type → Type 1 where
      | up (index : Index parents) : @Parser parents (parents.get index)
      | empty : @Parser parents α
      -- | eps {α : Type} [inst : BEq α] [inst : Hashable α] : HashSet α → Parser' α
      | eps : List α → @Parser parents α
      | term (predicate : Char → Prop) [{a : Char} → Decidable (predicate a)]
        : @Parser parents Char
      | map : (α → β) → @Parser (β :: parents) α → @Parser parents β
      | isNull : @Parser (α :: parents) α → @Parser parents α
      | or : @Parser (α :: parents) α → @Parser (α :: parents) α
        → @Parser parents α
      | andThen : @Parser ((α × β) :: parents) α → @Parser ((α × β) :: parents) β
        → @Parser parents (α × β)

  end
    namespace Parser

    #check (or (up ⟨0, _⟩) (term (. = 'c')) : Parser Char)

      -- def depends : (syn : Syntax α) → Nat
      --   | empty | eps _ | term _ => 0
      --   | map _ p | isNull p => p.size + 0
      --   | or p q | andThen p q => p.size + q.size + 0

      -- def expand : Syntax size α → Syntax size.succ α
      --   | empty => empty
      --   | eps parsed => eps parsed
      --   | term predicate => term predicate
      --   | or p q => (or p q.expand : Syntax (_ + (_ + 1) + 1) _)
      --   | andThen p q => (andThen p q.expand : Syntax (_ + (_ + 1) + 1) _)
      --   | map f p => map f p.expand
      --   | isNull p => isNull p.expand

    end Parser

  -- instance [inst : Repr α] : Repr (Syntax αs α) where
  --   reprPrec
  --     | Syntax.empty, _ => "empty"
  --     | Syntax.eps parsed, prec => Repr.addAppParen ("eps " ++ reprArg parsed) prec
  --     | Syntax.term predicate, prec => Repr.addAppParen ("term {predicate}") prec

  -- inductive Memo : (size : Nat) → Type 1 where
  --   | empty : Memo 0
  --   | push : Memo size → Syntax (refs : Refs) α → Memo size.succ

  -- def Memo (size : Nat) := {αs : List ((α : Type) ×' Ref size α) // αs.length < size}
  -- def Memo (size : Nat) := {syntaxes : List ((α : Type) ×' Syntax α) // syntaxes.length < size}

  -- inductive Memo : List Type → Type 1 where
  --   | empty : Memo []
  --   | cons : Memo old → Syntax α → Memo ((α :: depends) :: old)

  -- def Memo := List <| List <| (α : Type) ×' Syntax α

  -- structure Memo (size : Nat) where
  --   head : (α : Type) ×' Syntax size α
  --   syntaxes : List ((α : Type) ×' Syntax α)
  --   selfValid : head.snd.depends = syntaxes.length

  -- def Memo := List <| (α : Type) ×' Syntax α

  -- def Memo.conv (memo : Memo size) : Fin size = Index memo.syntaxes :=
  --   rw (Fin size = Fin .) memo.isValid rfl

  namespace Memo

    -- def head : Memo size.succ → (α : Type) ×' Syntax size α
    --   | push _ syn => syn

    -- def append : {initSize : Nat} → {tailSize : Nat} →
    --   Memo initSize → Memo tailSize → Memo (initSize + tailSize)
    -- | 0, tailSize, empty, tail => cast (rw (Memo tailSize = Memo .) (Nat.zero_add tailSize).symm rfl) tail
    -- | initSize + 1, tailSize, push init sym, tail => (append init tail).push sym

    -- def subMemo : {k : Nat} → (size : Nat) → Memo (k + size) → Memo size
    --   | 0, size, memo => cast (rw (Memo (0 + size) = Memo .) (Nat.zero_add size) rfl) memo
    --   | _, 0, push _ _ => empty
    --   | k + 1, size + 1, push memo _ =>
    --     let h : Memo (k + 1 + size) = Memo (k + size + 1) :=
    --       let h : k + 1 + size = k + size + 1 :=
    --         Eq.subst (Nat.add_right_comm k 1 size) rfl
    --       rw (Memo (k + 1 + size) = Memo .) h rfl
    --     subMemo (k := k) size.succ <| cast h memo

    -- def ref {size : Nat} (memo : Memo size.succ) : Ref size.succ memo.head.fst := Ref.mk

    -- def ref (memo : Memo) : Ref depends α := Ref.mk memo.length

    -- def get : {new : List <| List Type} →
    --   Memo (new ++ (α :: depends) :: old) → (ref : Ref (α :: depends) α) →
    --   Syntax (α :: depends) α
    --   | [], cons (_ : Memo old) (s : Syntax (α :: depends) α), _ => s
    --     -- match cast (rw (Memo ([] ++ α :: depends ++ old) = Memo .) (List.nil_append (α :: depends ++ old)) rfl) memo with
    --     -- match cast (
    --     --   rfl |>
    --     --     rw (Memo ([α] ++ old) = Memo .) (List.append_cons [] α old) |>
    --     --     rw (Memo ([] ++ α :: old) = Memo .) (List.nil_append (α :: old))
    --     --   ) memo with
    --       -- | cons (depends := []) (_ : Memo (depends ++ old)) (s : Syntax [α] α) => s
    --   -- | _ :: _, cons memo _, ref => get memo ref

    -- def push : {old depends : List Type} → (memo : Memo old) → Syntax (α :: depends) α → Memo (α :: depends ++ old)
    --   | old, [], memo, syn@Syntax.empty | old, [], memo, syn@(Syntax.eps _) => memo.cons syn
    --   | _, memo, syn@(Syntax.term _) => memo.cons (α := Char) syn
    --   | syn@(Syntax.map _ ref) | syn@(Syntax.isNull ref) => memo.push <| memo.get ref

    -- def register {size : Nat} {α : Type} (memo : Memo size) : Syntax depends α → Memo (size + depends + 1)
    --   | syn@Syntax.empty | syn@(Syntax.eps _) | syn@(Syntax.term _) => memo.push ⟨α, syn⟩
    --   | syn@(Syntax.map f p) => memo.push syn

  --   def get : {newer : List Type} → Memo (newer ++ α :: older) → (ref : Ref older α) → Syntax (α :: older) α
  --     | [], push _ s, _ => s
  --     | _ :: newer, push memo _, ref => @get α older newer memo ref

    -- def append : {size0 size1 : Nat} → Memo size0 → Memo size1 → Memo (size0 + size1)
    --   | 0, size1, empty, m =>
    --     let h : Memo size1 = Memo (0 + size1) :=
    --       rw (Memo . = Memo (0 + size1)) (Nat.zero_add size1) rfl
    --     cast h m
    --   | (Nat.succ size0), size1, @push _ refs0 α0 m0 (syn0 : Syntax refs0 α0), m1 => match refs0 with
    --     | Refs.zero =>
    --       let next : Memo (size0 + size1.succ) := append (size0 := size0) m0 <| m1.push syn0
    --       let h : Memo (size0 + size1).succ = Memo (size0.succ + size1) :=
    --         rw (Memo (size0 + size1).succ = Memo .) (Nat.succ_add size0 size1).symm rfl
    --       cast h next
    --     | Refs.one ref => _
    --     | Refs.same ref0 ref1 => _
    --     | Refs.two ref0 ref1 => _

  --   -- def get : Memo tys → (ref : Ref tys α) → Syntax tys α
  --   --   | @push tysTail α _ s, Ref.mk ⟨0, _⟩ same =>
  --   --     let tys := α :: tysTail
  --   --     cast (congrArg (λα => Syntax tys α) same) s
  --   --   | @push _ _ memo _, Ref.mk ⟨Nat.succ k, h⟩ same =>
  --   --     get memo <| Ref.mk ⟨k, Nat.le_of_succ_le_succ h⟩ same

  -- -- instance : Repr (Memo []) where
  -- --   reprPrec
  -- --     | Memo.empty, _ => "empty"

  -- -- instance : Repr (Memo (ty :: tys)) where
  -- --   reprPrec
  -- --     | Memo.push memo syn, prec => Repr.addAppParen ("push " ++ reprArg memo ++ reprArg syn) prec

  end Memo

  -- def Parser (α : Type) := Memo →
  --   (depends : List Nat) ×' Ref depends α × Memo

  -- def Parser (α : Type) := Memo → (Ref α × Memo)
  --   -- (depends : Nat) ×'
  --   --   Ref (depends + 1) α × (memo : Memo (depends + 1)) ×' α = memo.head.fst

  -- -- -- #reduce (Ref.self.shift : Ref [Nat, Nat] Nat)

  -- def parser (syn : Syntax α) : Parser α := λpred =>
  --   let memo := ⟨α, syn⟩ :: pred
  --   let ref := {
  --     size := memo.length
  --     index := ⟨pred.length,
  --       let goal : pred.length < memo.length := sorry
  --       goal
  --     ⟩
  --     isValid := λsyntaxes ok => rfl
  --   }
  --   (ref, memo)

  -- def parser : Syntax α → Parser α
  --   | syn@Syntax.empty | syn@(Syntax.eps _) | syn@(Syntax.term _) =>
  --     λmemo => ⟨[], Ref.mk memo.length, [⟨_, syn⟩] :: memo⟩
  --   | syn@(Syntax.map _ (Ref.mk p)) | syn@(Syntax.isNull (Ref.mk p)) =>
  --     λmemo => ⟨[p], Ref.mk memo.length, [⟨_, syn⟩] :: memo⟩
  --   | syn@(Syntax.or (Ref.mk p) (Ref.mk q)) | syn@(Syntax.andThen (Ref.mk p) (Ref.mk q)) =>
  --     λmemo => ⟨[p,q], Ref.mk memo.length, [⟨_, syn⟩] :: memo⟩

  -- def parser (syn : Syntax (α :: depends) α) : Parser α := λ{old} memo =>
  --   let memo := memo.push syn
  --   ⟨
  --     depends,
  --     (cast (rw (Memo (α :: depends ++ old) = Memo .) (List.nil_append (α :: depends ++ old)).symm rfl) memo).ref,
  --     memo
  --   ⟩

  -- def parser0 (syn : Syntax 0 α) : Parser α :=
  --   let memo := Memo.empty.push ⟨α, syn⟩
  --   ⟨0, memo.ref, memo, rfl⟩

  -- def map (f : α → β) : (p : Parser α) → Parser β
  --   | ⟨depends, ref, memo, _⟩ =>
  --     let memo := memo.push ⟨β, Syntax.map f ref⟩
  --     ⟨depends.succ, memo.ref, memo, rfl⟩

    -- ⟨{
    --   size := memo.size.succ
    --   head := ⟨α, syn⟩
    --   syntaxes := memo.head :: memo.syntaxes
    --   selfValid := rw (memo.size.succ = Nat.succ .) memo.selfValid rfl
    --   syntaxesValid := λ
    --     | List.Mem.head ⟨α, syn⟩ syntaxes => _
    -- }, _⟩

  -- def parser  (inBound : links ≤ size) (syn : Syntax (refs : Refs links) α) : Parser size α := λmemo =>
  --   let ref : Ref size.succ α := Ref.index ⟨size, Nat.succ_le_succ <| Nat.le_refl size⟩
  -- def parser (syn : {size : Nat} → Syntax size.succ α) : Parser α := λsize memoPred =>
  --   let head := ⟨α, (syn : Syntax size.succ α)⟩
  --   let expand : (α : Type) ×' Syntax size α → (α : Type) ×' Syntax size.succ α
  --     | ⟨α, syn⟩ => ⟨α, (Syntax.expand syn: Syntax size.succ α)⟩
  --   let tail := List.map expand memoPred.syntaxes
  --   let memo :=
  --     {
  --       syntaxes := head :: tail
  --       isValid :=
  --         let goal := Eq.refl size.succ
  --         let goal : size.succ = memoPred.syntaxes.length.succ :=
  --           rw (size.succ = Nat.succ .) memoPred.isValid goal
  --         let goal : size.succ = tail.length.succ :=
  --           rw (size.succ = Nat.succ .) (length_map expand memoPred.syntaxes) goal
  --         let goal : size.succ = (head :: tail).length :=
  --           rw (size.succ = .) (List.length_cons head tail).symm goal
  --         let goal : size.succ = (head :: tail).length :=
  --           rw (size.succ = .) goal rfl
  --         goal
  --     }
  --   let ref := Ref.mk ⟨0, Nat.zero_lt_succ size⟩
  --   let isValid :=
  --     let lhs := (List.get memo.syntaxes ⟨0, Eq.subst memo.isValid ref.index.isLt⟩).fst
  --     let goal := Eq.refl lhs
  --     let goal : lhs = head.fst := goal
  --     let goal : lhs = (⟨α, syn⟩ : (α : Type) ×' Syntax size.succ α).fst :=
  --       rw (lhs = PSigma.fst .) (rfl : head = (⟨α, syn⟩ : (α : Type) ×' Syntax size.succ α)) goal
  --     let goal : lhs = α := goal
  --     goal
  --   ⟨memo, ref, isValid⟩

  --   (ref, memo.push syn inBound)
  -- -- def parser (syn : Syntax (α :: tys) α) : Parser tys α := λmemo =>
  -- --   -- let h : 0 < (α :: tys).length :=
  -- --   --   let goal : 0 < [α].length + tys.length := Nat.le_add_right 1 tys.length
  -- --   --   let goal : 0 < ([α] ++ tys).length := Eq.subst (List.length_append [α] tys).symm goal
  -- --   --   let goal : 0 < (α :: tys).length := goal
  -- --   --   goal
  -- --   (Ref.mk, memo.push syn)

  -- def empty : Parser α := parser Syntax.empty
  -- def eps (parsed : List α) : Parser α := parser <| Syntax.eps parsed
  -- def term (predicate : Char → Prop) [{c : Char} → Decidable (predicate c)] : Parser Char :=
  --   parser <| Syntax.term predicate
  -- def or (p : Ref pDepends α) (q : Ref qDepends α) : Parser α :=
  --   parser <| Syntax.or p q
  -- def map (f : α → β) (p : Ref pDepends α) : Parser β :=
  --   parser <| Syntax.map f p

  -- def or (p : Parser α) (q : Parser α) : Parser α :=
  --   let ⟨pDepends, pRef, pMemo, pTypeMatch⟩ := p
  --   let ⟨qDepends, qRef, qMemo, qTypeMatch⟩ := q
  --   let memo := pMemo.push ⟨α, Syntax.or pRef qRef⟩
  --   ⟨pDepends + qDepends, memo.ref, memo, rfl⟩
  --   -- parser (Syntax.or p q)
  -- -- def or (p : Ref pIndex α) (q : Ref qIndex α)
  -- --     -- (pIsTail : ∃(newer : List Type), tys = newer ++ pTys)
  -- --     -- (qIsTail : ∃(newer : List Type), tys = newer ++ qTys)
  -- --   : Parser tys α := parser (Syntax.or p q)
  -- def map (f : α → β) (p : Ref size α) : Parser β := parser (Syntax.map f p)

  -- def char (c : Char) : Parser Char := term (c = .)

  -- def ex :=
  --   let ⟨_, p, memo⟩ := char 'a' []
  --   let ⟨_, q, memo⟩ := char 'b' []
  --   let ⟨_, r, memo⟩ := (or p q) []
  --   map Char.toNat r memo

  -- #reduce ex

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