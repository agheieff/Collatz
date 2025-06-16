import Lake
open Lake DSL

package «binary-collatz-proof» where
  -- Complete binary Collatz cycle proof

@[default_target]
lean_lib «BinaryCollatzComplete» where
  -- Self-contained proof module

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"