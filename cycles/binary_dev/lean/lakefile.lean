import Lake
open Lake DSL

package «collatz-cycles» where
  -- add package configuration options here

lean_lib «CollatzCycles» where
  -- add library configuration options here

lean_lib «BinaryCycles» where
  -- Binary Collatz cycles impossibility proof

lean_lib «BinaryCollatz» where
  -- Main module for binary Collatz results

@[default_target]
lean_exe «collatz-cycles» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"