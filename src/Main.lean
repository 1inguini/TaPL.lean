-- import arith
-- import tyarith

def testLanguage (langName : String) (langMain : String → IO Unit) : List System.FilePath → IO Unit
| [] => 
  let evalFile file := do
    IO.println <| "Evaluating " ++ file ++ " ..."
    IO.FS.readFile (System.mkFilePath ["examples", langName, file]) >>= langMain
  do
    IO.println <| "Testing " ++ langName
    evalFile "test.f"
    evalFile "test_ex.f"
| files =>
  files.forM (λsrc => IO.FS.readFile src >>= langMain)

def main : List String -> IO Unit
-- | "arith" :: files => test_language "arith" arith.main files
-- | "tyarith" :: files => test_language "tyarith" tyarith.main files
| name :: _ => IO.println <| "Language " ++ name ++ " is not implemented yet."
| [] => IO.println "usage: Pass a language name to test it."
