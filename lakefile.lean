import Lake
open Lake DSL

package math {
  -- add package configuration options here
}

lean_lib Math {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe math {
  root := `Main
}
