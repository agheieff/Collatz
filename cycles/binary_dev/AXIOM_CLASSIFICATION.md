# Classification of Axioms in ProofAxioms.lean

## Purely Computational (Can be verified by computation)
1. **log2_3_bounds**: log₂(3) ∈ (1.584, 1.586)
   - Status: Computational, standard mathematical constant
   - Priority: LOW - well-known value

2. **no_cycles_small_k**: No cycles for k ≤ 100
   - Status: Computational, requires exhaustive search
   - Priority: MEDIUM - needed for completeness

3. **verified_k_2_to_20**: Specific small k checked
   - Status: Computational, already verified
   - Priority: LOW - subset of no_cycles_small_k

4. **count_mod_8_eq_1**: Counting residue classes
   - Status: Mathematical fact, not really an axiom
   - Priority: LOW - standard number theory

## Theoretical Results (Should be proven, not axioms)
1. **cycle_equation_axiom**: n₁(2^J - 3^k) = C
   - Status: PROVEN in CycleEquationClean.lean
   - Action: Remove axiom, import proof

2. **j_sum_lower_bound**: J > ⌊1.585k⌋
   - Status: PROOF STRUCTURE COMPLETE in JSumLowerBoundProof.lean
   - Action: Complete numerical verification

3. **C_growth_cycle_compatible**: C grows like 3^k
   - Status: Needs proof based on sum structure
   - Priority: CRITICAL - fixes old false bound

4. **C_ratio_decreasing**: C/4^k decreases for k ≥ 8
   - Status: PROOF FRAMEWORK in CRatioDecreasingProof.lean
   - Priority: CRITICAL - key to medium-J case

## Technical Lemmas (Should be proven)
1. **nat_div_property**: k - k/10 ≥ 9k/10
   - Status: Basic arithmetic
   - Priority: LOW - trivial

2. **exp_dominates_linear**: For k > 1000, 9k/10 > 2^k/8 is false
   - Status: Basic analysis
   - Priority: LOW - standard exponential growth

3. **j2_mod_4_complete**, **j2_mod_8_complete**: Modular properties
   - Status: Direct computation from binaryCollatz definition
   - Priority: MEDIUM - needed for modular analysis

## Diophantine/Analytic Results (Legitimate axioms or need deep theory)
1. **crisis_density**: Crisis points are rare
   - Status: Follows from Dirichlet approximation theory
   - Could remain as axiom or prove using measure theory

2. **denominator_bound_non_crisis**: Lower bound on |2^J - 3^k|
   - Status: Deep result from Diophantine approximation
   - Legitimate axiom or needs Baker's theorem

3. **three_k_over_k_dominates**: 3^k/k dominates 2^k
   - Status: Basic but needs careful proof
   - Priority: MEDIUM

## Action Items
1. Remove cycle_equation_axiom - already proven
2. Complete j_sum_lower_bound proof (just needs log₂(3) verification)
3. Prove C_growth_cycle_compatible and C_ratio_decreasing
4. Convert simple arithmetic lemmas to proofs
5. Keep only truly deep results as axioms