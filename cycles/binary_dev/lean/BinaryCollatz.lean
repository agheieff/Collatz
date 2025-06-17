/-!
# Binary Collatz Cycles

Main module that exports the binary Collatz cycles impossibility theorem.
-/

import BinaryCycles.FinalTheoremComplete

-- Re-export the main theorems
export BinaryCollatz (binary_collatz_cycles_impossible)
export BinaryCollatz (binary_collatz_conjecture)
export BinaryCollatz (no_nontrivial_binary_cycles)
export BinaryCollatz (binary_collatz_no_cycles)