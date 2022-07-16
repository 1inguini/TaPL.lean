import Lake
open Lake DSL

package TaPL {
}

lean_lib TaPL {
  srcDir := "src"
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