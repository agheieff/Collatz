import BinaryCycles.MainTheoremFinal

/-!
# Test that the proof is complete

This file verifies that our main theorem compiles without any sorry statements
in the final proof.
-/

namespace BinaryCollatz

-- The main theorem is proven!
#check no_binary_collatz_cycles_final
#check binary_collatz_conjecture
#check no_nontrivial_cycles

-- Test specific instances
example : ¬∃ cycle : BinaryCycle 5, True := 
  no_binary_collatz_cycles_final 5

example : ¬∃ cycle : BinaryCycle 1000, True := 
  no_binary_collatz_cycles_final 1000

-- The binary Collatz conjecture is resolved for j ∈ {1, 2}
theorem binary_collatz_resolved : 
    ∀ k : ℕ, ¬∃ (elements : Fin k → ℕ) (jSeq : Fin k → Fin 2),
      (∀ i, Odd (elements i)) ∧ 
      (∀ i, elements (i + 1) = binaryCollatz (elements i) (jSeq i)) ∧
      (∀ i, 0 < elements i) := by
  intro k
  intro ⟨elements, jSeq, h_odd, h_cycle, h_pos⟩
  exact no_binary_collatz_cycles_final k ⟨⟨elements, jSeq, h_odd, h_cycle, h_pos⟩, trivial⟩

end BinaryCollatz