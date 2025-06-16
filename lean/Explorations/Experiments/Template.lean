/-!
# Experiment Template

Use this template when exploring new ideas. Follow the methodology:
1. State the conjecture/idea clearly
2. Formalize all definitions
3. Attempt the proof
4. If successful, move to appropriate directory
5. If unsuccessful, document why it fails
-/

namespace CollatzExperiment

/-- Example: Exploring a new pattern in Collatz sequences -/
def interesting_property (n : ℕ) : Prop := sorry

/-- Conjecture: This property implies something useful -/
theorem property_implies_bound (n : ℕ) (h : interesting_property n) :
  n < 2^100 := by
  sorry -- Attempt proof here

/-- Why this approach failed (if applicable) -/
/-
This approach failed because:
1. The property is too weak to imply the bound
2. Counterexample: n = ...
3. Need stronger assumptions
-/

end CollatzExperiment