import BinaryCycles.Core
import BinaryCycles.Axioms
import BinaryCycles.NumericalBounds

/-!
# Medium-J Analysis for Binary Collatz Cycles

This file analyzes the medium-J case where J is neither high nor in crisis.

## Status: INCOMPLETE
The original proof relied on C/4^k → 0 to show contradiction.
With the corrected C ~ 3^k growth, this approach fails.
A new contradiction mechanism is needed.

## The Gap
- C ~ 3^k and denominator ~ δ·3^k for non-crisis
- This gives n₁ ~ constant (doesn't grow with k)
- Original counting argument no longer works
-/

namespace BinaryCollatz

open Real

/-! ## Medium-J Definition and Properties -/

/-- Medium-J: not high-J and not crisis -/
def isMediumJ (k : ℕ) (J : ℕ) : Prop :=
  ⌊1.585 * k⌋ < J ∧ J < 2 * k - k / 10 ∧ ¬isCrisis k

/-- In medium-J, we have moderate number of j=2 positions -/
theorem medium_j_structure (k : ℕ) (J : ℕ) (h_med : isMediumJ k J) :
    let num_j2 := J - k
    k / 10 < num_j2 ∧ num_j2 < 9 * k / 10 := by
  sorry

/-! ## Element Bounds (The Problem Area) -/

/-- For medium-J non-crisis, n₁ is bounded by a constant -/
theorem n1_bounded_constant (k : ℕ) (cycle : BinaryCycle k)
    (hk : k > 100) (h_med : isMediumJ k (sumJ k cycle.jSeq)) :
    ∃ M : ℝ, M > 0 ∧ (cycle.elements 0 : ℝ) ≤ M := by
  -- This is the KEY ISSUE with the original proof
  -- With C ~ c₁·3^k and denominator ~ δ·3^k
  -- We get n₁ = C/denominator ~ c₁/δ = constant
  
  let J := sumJ k cycle.jSeq
  
  -- Get C bounds
  have ⟨c₁, c₂, _, _, _, _, hC_upper⟩ := 
    C_growth_cycle_compatible k cycle.jSeq 
      ⟨h_med.1, by linarith : J < 2 * k⟩
  
  -- Get denominator bound (non-crisis)
  have ⟨δ, hδ_pos, h_denom⟩ := 
    denominator_bound_non_crisis k J ⟨h_med.1, h_med.2.1⟩ h_med.2.2
  
  -- Apply cycle equation
  have h_n1 := n1_from_cycle_equation k cycle (by omega : 0 < k)
  
  -- Calculate upper bound
  use c₂ / δ
  constructor
  · apply div_pos; linarith
  · calc (cycle.elements 0 : ℝ)
      = (computeC k cycle.jSeq : ℝ) / |2^J - 3^k| := h_n1
      _ ≤ c₂ * 3^k / (δ * 3^k) := by
        apply div_le_div
        · exact hC_upper
        · linarith
        · exact h_denom
        · apply mul_pos hδ_pos; apply pow_pos; norm_num
      _ = c₂ / δ := by field_simp

/-- All cycle elements have similar bounds -/
theorem cycle_elements_similar_bounds (k : ℕ) (cycle : BinaryCycle k)
    (hk : k > 100) (h_med : isMediumJ k (sumJ k cycle.jSeq)) :
    ∃ M : ℝ, M > 0 ∧ ∀ i : Fin k, (cycle.elements i : ℝ) ≤ M * k := by
  -- In medium-J, elements don't grow much through the cycle
  -- This is because (3n+1)/2^j ≈ (3/2^j)n for large n
  sorry

/-! ## The Failed Approach -/

/-- OBSOLETE: The original counting argument doesn't work -/
theorem medium_j_old_approach_fails (k : ℕ) (cycle : BinaryCycle k)
    (hk : k > 100) (h_med : isMediumJ k (sumJ k cycle.jSeq)) :
    -- Cannot conclude False from bounded elements alone
    True := by
  -- Original approach:
  -- 1. Show all elements ≤ M for constant M
  -- 2. But need k distinct odd integers
  -- 3. Claim: not enough odd integers ≤ M
  
  -- Why this fails:
  -- M could be large enough to contain k distinct odd integers
  -- Without growth in M relative to k, no contradiction
  trivial

/-! ## The Width Constraint Approach -/

/-- The width constraint provides the contradiction for medium-J -/
theorem medium_j_width_contradiction (k : ℕ) (cycle : BinaryCycle k)
    (hk : k > 10000) (h_med : isMediumJ k (sumJ k cycle.jSeq)) :
    False := by
  -- Key insight: Elements must satisfy two incompatible constraints
  
  -- 1. Boundedness: All elements in range [M/C, MC] for constants M, C
  -- This follows from n₁ ~ constant and bounded growth ratios
  obtain ⟨M, hM_pos, h_n1⟩ := n1_bounded_constant k cycle (by omega : k > 100) h_med
  
  -- 2. Distinctness: Need k distinct odd integers
  -- Minimum width for k distinct odd integers is 2(k-1)
  
  -- But the range [M/C, MC] contains only O(M) odd integers
  -- For large k, we can't fit k distinct odd integers in this range
  
  -- The formal proof would follow WidthConstraint.lean
  sorry -- Will be completed when width constraint is fully formalized

/-- Alternative: Counting odd integers in bounded range -/
theorem medium_j_counting_contradiction (k : ℕ) (cycle : BinaryCycle k)
    (hk : k > 10000) (h_med : isMediumJ k (sumJ k cycle.jSeq)) :
    False := by
  -- All cycle elements are odd integers in a bounded range
  -- But for large k, there aren't enough odd integers in any bounded range
  
  -- Get bounds on all elements
  obtain ⟨M, hM_pos, h_bounds⟩ := cycle_elements_similar_bounds k cycle (by omega : k > 100) h_med
  
  -- Count odd integers in range [1, M*k]
  -- At most (M*k)/2 odd integers
  
  -- But we need k distinct odd integers
  -- For large k, k > (M*k)/2 is impossible when M is constant
  
  sorry -- Technical counting argument

/-! ## Partial Results -/

/-- j-pattern constraints in medium-J -/
theorem medium_j_pattern_constraints (k : ℕ) (seq : BinaryJSeq k)
    (h_med : isMediumJ k (sumJ k seq)) :
    -- Some structural constraint on j-patterns
    -- This might be the key to a new approach
    sorry := by
  sorry

/-- Element ratios in medium-J cycles -/
theorem medium_j_element_ratios (k : ℕ) (cycle : BinaryCycle k)
    (h_med : isMediumJ k (sumJ k cycle.jSeq)) :
    ∀ i : Fin k, 
    let ratio := (cycle.elements (i + 1) : ℝ) / cycle.elements i
    1/2 < ratio ∧ ratio < 2 := by
  -- Elements can't vary too much in a cycle
  sorry

end BinaryCollatz