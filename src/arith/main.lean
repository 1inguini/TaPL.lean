import system.io
import data.buffer
import data.buffer.parser

namespace arith

  namespace parser

  end parser

  def str : string := "hello fron arith"

end arith

def main : io unit :=
  io.put_str_ln arith.str
