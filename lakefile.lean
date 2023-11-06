import Lake
open Lake DSL

require mathlib from git
    "https://github.com/leanprover-community/mathlib4"

package «s_box_complement» {
  -- add package configuration options here
}

lean_lib «SBoxComplement» {
  -- add library configuration options here
}

@[default_target]
lean_exe «s_box_complement» {
  root := `Main
}
