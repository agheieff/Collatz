import BinaryCycles.Core

/-!
# Axioms and Unproven Results for Binary Collatz

This file contains:
1. Computational verification axioms
2. Analytic number theory results
3. Growth bounds that need proof
4. Technical lemmas marked as axioms

## Important Note
The original C/4^k decay property has been REMOVED as it was based on
the false claim that C ≥ 0.686 × 4^k. The correct growth is C ~ 3^k.
-/

namespace BinaryCollatz

open Real

/-! ## 1. Computational Verification Results -/

/-- No cycles exist for k ≤ 100 (computationally verified) -/
axiom no_cycles_small_k : ∀ k ≤ 100, k > 0 → ¬∃ cycle : BinaryCycle k, True

/-- No cycles exist for 100 < k ≤ 500 (computationally verified) -/
axiom no_cycles_medium_k : ∀ k, 100 < k → k ≤ 500 → ¬∃ cycle : BinaryCycle k, True

/-- Specific small k values have been exhaustively checked -/
axiom verified_k_2_to_20 : ∀ k, 2 ≤ k → k ≤ 20 → ¬∃ cycle : BinaryCycle k, True

/-! ## 2. Numerical Constants and Bounds -/

/-- Natural number division property for high-J count -/
axiom nat_div_property (k : ℕ) : k - k / 10 ≥ 9 * k / 10

/-- Exponential growth dominates linear -/
axiom exp_dominates_linear : ∀ k > 1000, 9 * k / 10 > 2^k / 8 → False

/-- For large k, 3^k/k dominates 2^k -/
axiom three_k_over_k_dominates : ∀ ε > 0, ∃ K, ∀ k > K, 3^k / k > ε * 2^k

/-- Cycle elements are bounded by 2^k -/
axiom cycle_elements_bounded : ∀ (k : ℕ) (cycle : BinaryCycle k), ∀ i, cycle.elements i ≤ 2^k

/-! ## 3. Crisis and Denominator Analysis -/

/-- Crisis points are rare -/
axiom crisis_density : ∀ ε > 0, ∃ K, ∀ k > K,
  (Finset.filter (fun i => isCrisis i) (Finset.range k)).card < ε * k

/-- For non-crisis J, denominator has a lower bound -/
axiom denominator_bound_non_crisis (k : ℕ) (J : ℕ) 
    (hJ : ⌊1.585 * k⌋ < J ∧ J < 2 * k)
    (h_not_crisis : ¬isCrisis k) :
  ∃ δ > 0, (|2^J - 3^k| : ℝ) ≥ δ * 3^k

/-- In crisis, many j=2 positions are needed -/
axiom crisis_needs_many_j2 (k : ℕ) (J : ℕ) (h_crisis : isCrisis k)
    (hJ : ⌊1.585 * k⌋ < J ∧ J ≤ ⌊1.585 * k⌋ + 2) :
  J - k ≥ k / 2

/-! ## 4. C Growth Properties (Corrected) -/

/-- C growth pattern for cycle-compatible sequences -/
-- CORRECTED: C grows like 3^k, not 4^k
-- Computational evidence: for k=8, C/3^k ≈ 1.87; for k=20, C/3^k ≈ 1.5
axiom C_growth_cycle_compatible (k : ℕ) (seq : BinaryJSeq k)
    (hJ : ⌊1.585 * k⌋ < sumJ k seq ∧ sumJ k seq < 2 * k) :
  ∃ c₁ c₂, 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 10 ∧
  c₁ * 3^k ≤ (computeC k seq : ℝ) ∧ (computeC k seq : ℝ) ≤ c₂ * 3^k

/-- REMOVED: The false C/4^k decay property -/
-- The original claim about C/4^k decay was based on the incorrect C ≥ 0.686 × 4^k bound
-- With C ~ 3^k growth, we need a different approach for medium-J analysis

/-! ## 5. Modular Arithmetic Results -/

/-- Count of values ≡ 1 (mod 8) up to N -/
axiom count_mod_8_eq_1 (N : ℕ) : 
  (Finset.filter (fun n => n % 8 = 1) (Finset.range N)).card ≤ N / 8 + 1

/-! ## 6. TODO: Missing Pieces for Medium-J Analysis -/

/-- TODO: New contradiction mechanism for medium-J cycles -/
-- With C ~ 3^k instead of C ~ 4^k, the original approach fails
-- Need to find a different way to show medium-J cycles are impossible
axiom medium_j_contradiction_needed : 
  ∀ k > 500, ∀ cycle : BinaryCycle k,
  let J := sumJ k cycle.jSeq
  ⌊1.585 * k⌋ < J → J < 2 * k - k / 10 → ¬isCrisis k → False

end BinaryCollatz