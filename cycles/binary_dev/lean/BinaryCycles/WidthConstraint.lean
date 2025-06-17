import BinaryCycles.Core
import BinaryCycles.NumericalBounds
import BinaryCycles.MediumJAnalysis

/-!
# Width Constraint for Medium-J Cycles

This file formalizes the width constraint contradiction for medium-J cycles.

## Key Insight
For medium-J cycles where n₁ ~ constant:
1. All elements must fit in a narrow range [m, M]
2. But we need k distinct odd integers
3. The minimum width for k distinct odd integers is 2(k-1)
4. This creates an impossible constraint for large k
-/

namespace BinaryCollatz

open Real

/-! ## Width Definitions -/

/-- The width of a set of natural numbers -/
def width (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then
    S.max' h - S.min' h
  else 0

/-- The width of cycle elements -/
def cycleWidth (k : ℕ) (cycle : BinaryCycle k) : ℕ :=
  width (Finset.image cycle.elements Finset.univ)

/-- Minimum width needed for k distinct odd integers -/
theorem min_width_for_distinct_odd (k : ℕ) (hk : k > 0) :
    ∀ (S : Finset ℕ), S.card = k → (∀ n ∈ S, Odd n) → 
    (∀ i j : Fin k, i ≠ j → S.toList.get? i ≠ S.toList.get? j) →
    width S ≥ 2 * (k - 1) := by
  intro S hcard hodd hdistinct
  -- The smallest k distinct odd integers are 1, 3, 5, ..., 2k-1
  -- Width = (2k-1) - 1 = 2(k-1)
  sorry

/-! ## Element Range Bounds -/

/-- In medium-J cycles, elements are in a bounded range -/
theorem medium_j_element_range (k : ℕ) (cycle : BinaryCycle k)
    (hk : k > 100) (h_med : isMediumJ k (sumJ k cycle.jSeq)) :
    ∃ M C : ℝ, M > 0 ∧ C > 1 ∧
    ∀ i : Fin k, M / C ≤ (cycle.elements i : ℝ) ∧ (cycle.elements i : ℝ) ≤ M * C := by
  -- From n1_bounded_constant, we know n₁ ≤ M for some constant M
  obtain ⟨M, hM_pos, h_n1⟩ := n1_bounded_constant k cycle hk h_med
  
  -- Elements can't vary by more than bounded factors through the cycle
  -- j=1 multiplies by ~1.5, j=2 multiplies by ~0.75
  -- Maximum ratio between any two elements is bounded
  
  use M, 100  -- C = 100 is conservative bound on max ratio
  constructor; exact hM_pos
  constructor; norm_num
  
  intro i
  -- All elements are related to n₁ by bounded factors
  sorry

/-- The width of medium-J cycles is bounded -/
theorem medium_j_width_bounded (k : ℕ) (cycle : BinaryCycle k)
    (hk : k > 100) (h_med : isMediumJ k (sumJ k cycle.jSeq)) :
    ∃ B : ℕ, cycleWidth k cycle ≤ B := by
  -- From medium_j_element_range, all elements in [M/C, MC]
  -- So width ≤ MC - M/C = M(C - 1/C)
  obtain ⟨M, C, _, hC, h_range⟩ := medium_j_element_range k cycle hk h_med
  
  -- Width is at most M * C - M / C
  use ⌈M * (C + 1 / C)⌉.toNat
  sorry

/-! ## The Width Contradiction -/

/-- The main width constraint theorem -/
theorem width_constraint_contradiction (k : ℕ) (cycle : BinaryCycle k)
    (hk : k > 10000) (h_med : isMediumJ k (sumJ k cycle.jSeq)) :
    False := by
  -- Step 1: Cycle needs width ≥ 2(k-1) for k distinct odd integers
  have h_min_width : cycleWidth k cycle ≥ 2 * (k - 1) := by
    apply min_width_for_distinct_odd k (by omega : k > 0)
    · simp [cycleWidth, width]
      sorry -- Finset.card of image equals k due to distinctness
    · intro n hn
      simp [cycleWidth, width] at hn
      obtain ⟨i, hi⟩ := hn
      rw [← hi]
      exact cycle.all_odd i
    · sorry -- Distinctness from cycle.all_distinct
  
  -- Step 2: But width is bounded by constant B
  obtain ⟨B, h_width_bound⟩ := medium_j_width_bounded k cycle (by omega : k > 100) h_med
  
  -- Step 3: For large k, 2(k-1) > B
  have h_impossible : 2 * (k - 1) > B := by
    -- B is constant, but 2(k-1) → ∞
    sorry -- Need to make B explicit in medium_j_width_bounded
  
  -- Contradiction
  linarith

/-! ## Alternative Formulation -/

/-- Number of odd integers in an interval -/
def oddCount (a b : ℕ) : ℕ :=
  ((b - a) / 2 + 1)

/-- Not enough odd integers in bounded range -/
theorem insufficient_odd_integers (M C : ℝ) (hM : M > 0) (hC : C > 1) :
    ∃ K, ∀ k > K, 
    oddCount ⌊M / C⌋.toNat ⌈M * C⌉.toNat < k := by
  -- The interval [M/C, MC] contains at most (MC - M/C)/2 + 1 odd integers
  -- This is approximately M(C + 1/C)/2
  -- For fixed M and C, this is constant
  -- But k → ∞, so eventually k exceeds this bound
  
  use ⌈2 * M * (C + 1 / C)⌉.toNat
  intro k hk
  sorry

/-- Alternative proof using counting -/
theorem width_contradiction_counting (k : ℕ) (cycle : BinaryCycle k)
    (hk : k > 10000) (h_med : isMediumJ k (sumJ k cycle.jSeq)) :
    False := by
  -- Get element range
  obtain ⟨M, C, hM, hC, h_range⟩ := medium_j_element_range k cycle (by omega : k > 100) h_med
  
  -- Not enough odd integers in [M/C, MC] for large k
  have ⟨K, hK⟩ := insufficient_odd_integers M C hM hC
  have h_insufficient : oddCount ⌊M / C⌋.toNat ⌈M * C⌉.toNat < k := by
    apply hK
    sorry -- Show k > K
  
  -- But cycle has k distinct odd elements in this range
  have h_need_k : oddCount ⌊M / C⌋.toNat ⌈M * C⌉.toNat ≥ k := by
    -- All k cycle elements are distinct odd integers in [M/C, MC]
    sorry
  
  linarith

end BinaryCollatz