import Lake
open Lake DSL

package TaPL {
  srcDir := "src"
}

lean_lib library {
  roots := #[]
}

@[defaultTarget]
lean_exe executable {
  exeName := "TaPL"
  root := `Main
}