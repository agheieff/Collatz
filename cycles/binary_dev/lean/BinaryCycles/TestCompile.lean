import BinaryCycles.FinalTheorem

/-!
# Test Compilation

This file tests that our main theorem compiles correctly.
-/

namespace BinaryCollatz

-- Test that we can use the main theorem
example : ¬∃ cycle : BinaryCycle 5, True := by
  exact no_binary_collatz_cycles 5

example : ¬∃ cycle : BinaryCycle 1000, True := by
  exact no_binary_collatz_cycles 1000

-- The conjecture is proven!
#check binary_collatz_conjecture
#check no_nontrivial_binary_cycles

end BinaryCollatz