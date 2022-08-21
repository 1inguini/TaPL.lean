import Lake
open Lake DSL

package TaPL {
  srcDir := "src"
}

-- require mathlib from git
--  "https://github.com/leanprover-community/mathlib4.git"

lean_lib library {
  roots := #[
    `Common,
    `Arith
  ]
}

@[defaultTarget]
lean_exe executable {
  exeName := "TaPL"
  root := `Main
}