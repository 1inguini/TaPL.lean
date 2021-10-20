import arith
import tyarith

private def traverse {m : Type → Type} [monad m] {α β : Type} (f : α → m β) : list α → m (list β)
| [] := pure []
| (x :: xs) := do
  y ← f x,
  ys ← traverse xs,
  pure $ y :: ys

def test_language (lang_name : string) (lang_main : char_buffer → io unit) (args : list string) : io unit := 
  let path := "examples/" ++ lang_name ++ "/"
  in match args with 
    | [] := do
        io.put_str_ln $ "Testing " ++ lang_name,
        io.put_str_ln $ "Evaluating test.f ...",
        io.fs.read_file (path ++ "test.f") >>= lang_main,
        io.put_str_ln $ "Evaluating test_ex.f ...",
        io.fs.read_file (path ++ "test_ex.f") >>= lang_main
    | files := do
      unit.star <$ traverse (λsrc, io.fs.read_file src >>= lang_main) files
    end

def main : io unit := do
  args ← io.cmdline_args,
  match args with
  | "arith" :: files := test_language "arith" arith.main files
  | "tyarith" :: files := test_language "tyarith" tyarith.main files
  | name :: _ := io.put_str_ln $ "Language " ++ name ++ " is not implemented yet."
  | [] := io.put_str_ln "usage: Pass a language name to test it."
  end
