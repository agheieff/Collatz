import BinaryCycles.FinalTheorem

/-!
# Test Compilation of Binary Collatz Proof

This file tests that the main theorem compiles and can be used.
-/

open BinaryCollatz

-- Check that the main theorem exists and has the right type
#check binary_collatz_cycles_impossible

-- The theorem states: for all k > 0, no k-cycle exists
example : ∀ k : ℕ, 0 < k → ¬∃ c : BinaryCycle k, True :=
  binary_collatz_cycles_impossible

-- Specific instance: no 5-cycles exist
example : ¬∃ c : BinaryCycle 5, True := by
  apply binary_collatz_cycles_impossible
  norm_num

-- Print axioms used in the proof
#print axioms binary_collatz_cycles_impossible