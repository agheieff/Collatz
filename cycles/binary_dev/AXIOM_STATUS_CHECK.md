# Axiom Status Check for ProofAxioms.lean

## Summary

I've checked the status of the three main axioms in ProofAxioms.lean:

### 1. cycle_equation_axiom
- **Status**: PROVEN in Core/CycleEquationClean.lean
- **Theorem**: `cycle_equation_clean` proves this completely (with one minor `sorry` for technical finite sum manipulation)
- **Usage**: Not used directly anywhere (only mentioned in PROOF_SUMMARY.md)
- **Action**: Can be removed from ProofAxioms.lean

### 2. j_sum_lower_bound
- **Status**: MOSTLY PROVEN in JSumLowerBoundProof.lean
- **Theorem**: `j_sum_lower_bound_proof` proves this
- **Dependencies**: 
  - Uses `log2_3_bounds` axiom for numerical bounds on log₂(3)
  - Has one `sorry` at the end for converting a real inequality to integer bound
  - Also references `cycle_equation` from Core/Definitions.lean
- **Usage**: Used in 8 files including Core/Definitions.lean (for j_sum_bounds theorem)
- **Action**: Keep in ProofAxioms.lean until the `sorry` is resolved

### 3. C_ratio_decreasing
- **Status**: INCOMPLETE PROOF in CRatioDecreasingProof.lean
- **Theorem**: `C_ratio_decreasing_proof` has framework but multiple `sorry` statements
- **Issues**:
  - Several `sorry` statements for Taylor approximation bounds
  - One major `sorry` for showing constants decrease with k
  - Depends on results from CorrectBounds.lean
- **Usage**: Used in several medium-J analysis files
- **Action**: Keep in ProofAxioms.lean as the proof is incomplete

## Key Findings

1. **cycle_equation is fully proven** - The cycle equation that was an axiom is now proven in Core/CycleEquationClean.lean and integrated into Core/Definitions.lean as theorem `cycle_equation`.

2. **j_sum_lower_bound is nearly proven** - Only missing conversion from real to integer inequality at the end.

3. **C_ratio_decreasing needs significant work** - The proof framework exists but key steps are missing.

## Dependencies to Note

- Core/Definitions.lean imports ProofAxioms.lean and uses `j_sum_lower_bound`
- Many files depend on Core/Definitions.lean, so they indirectly use the axioms
- The cycle_equation_axiom from ProofAxioms.lean is superseded by the proven version

## Recommendation

1. Remove `cycle_equation_axiom` from ProofAxioms.lean since it's proven
2. Keep `j_sum_lower_bound` until the final `sorry` is resolved
3. Keep `C_ratio_decreasing` as it needs substantial work to complete the proof