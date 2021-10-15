import system.io
import data.buffer
import data.buffer.parser

namespace arith

  namespace ast

    structure info := (index : nat)

    inductive term : Type
    | true : info -> term
    | false : info -> term
    | if_then_else : info -> term -> term -> term -> term
    | is_zero : info -> term -> term
    | zero : info -> term
    | succ : info -> term -> term
    | pred : info -> term -> term

  end ast

  namespace parser

  end parser

  def str : string := "hello fron arith"

end arith

def main : io unit :=
  io.put_str_ln arith.str
