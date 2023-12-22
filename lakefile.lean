import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.2.0"

package «learning-lean»

@[default_target]
lean_lib «Cpdt»

@[default_target]
lean_lib «ℕGame»

@[default_target]
lean_lib «SoftwareFoundations»

@[default_target]
lean_lib «Tapl»

@[default_target]
lean_lib «Tpil»

@[default_target]
lean_lib «Greeting»

@[default_target]
lean_lib «Fpil»

@[default_target]
lean_exe «greeting» where
  root := `Greeting.Main

@[default_target]
lean_exe «feline» where
  root := `Feline.Main
