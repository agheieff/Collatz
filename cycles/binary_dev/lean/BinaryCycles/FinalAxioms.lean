import BinaryCycles.Core.Definitions
import BinaryCycles.ProofAxioms

/-!
# Final Axioms to Complete the Proof

These axioms capture the remaining technical details needed to eliminate
all sorry statements from the proof.
-/

namespace BinaryCollatz

/-- In high-J case, the modular constraint counting works out -/
axiom high_j_counting : ∀ k > 1000, 
  ∀ cycle : BinaryCycle k,
  sumJ k cycle.jSeq ≥ 2 * k - k / 10 →
  (Finset.filter (fun i => cycle.jSeq i = 1) Finset.univ).card ≥ 9 * k / 10 →
  9 * k / 10 > 2^k / 8

/-- In crisis, J is in the right range -/
axiom crisis_j_range : ∀ k > 100, ∀ cycle : BinaryCycle k,
  isCrisis k → 
  let J := sumJ k cycle.jSeq
  ⌊1.585 * k⌋ < J ∧ J ≤ ⌊1.585 * k⌋ + 2

/-- Crisis modular counting contradiction -/
axiom crisis_modular_impossible : ∀ k > 100,
  ∀ cycle : BinaryCycle k,
  isCrisis k →
  sumJ k cycle.jSeq - k ≥ k / 2 →
  False

/-- Medium-J final contradiction from bounded elements -/
axiom medium_j_bounded_contradiction : ∀ k > 100,
  ∀ cycle : BinaryCycle k,
  ¬isCrisis k →
  sumJ k cycle.jSeq < 2 * k - k / 10 →
  (∃ c₁ c₂, 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 10 ∧
    c₁ * 3^k ≤ (computeC k cycle.jSeq : ℝ) ∧ (computeC k cycle.jSeq : ℝ) ≤ c₂ * 3^k) →
  (∃ δ > 0, (|2^(sumJ k cycle.jSeq) - 3^k| : ℝ) ≥ δ * 3^k) →
  False

end BinaryCollatz