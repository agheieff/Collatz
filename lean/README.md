# Lean Formalization of Collatz Cycle Analysis

This directory contains a formal verification in Lean 4 of the key findings about binary Collatz cycles.

## Files

- **CollatzCycles.lean**: Core definitions and main theorems
  - Definition of k-cycles and j-sequences
  - Fundamental constraints (sum bounds, closure equation)
  - Main bounds on closure constant C
  - Growth bounds and specific impossibility results

- **BinaryCycles.lean**: Detailed analysis of binary j-sequences
  - Configuration space of j=1 positions
  - Extremal configuration theorem
  - Tail₂ analysis and forcing mechanisms
  - Empirical bounds on C/4^k

- **DenominatorCrisis.lean**: The denominator crisis phenomenon
  - Weyl equidistribution and fractional parts
  - Critical k values where denominator becomes tiny
  - Forced arithmetic constraints
  - Connection to continued fractions

## Status

All theorems are stated but proofs are marked with `sorry`. This reflects the current state of the mathematical research:

- **Proven (needs formalization)**: 
  - Closure constant bounds
  - Extremal configuration analysis
  - Basic impossibility results (no cycles with 1,2,3 ones)
  - Denominator crisis via Weyl equidistribution

- **Empirically verified**:
  - C/4^k ≥ 0.686 for all tested cases
  - No binary cycles for k ≤ 40
  - Critical k values match theoretical predictions

- **Open**:
  - Complete proof that denominator crisis creates contradiction
  - Explicit bounds making exhaustive search feasible

## Building

These files are written for Lean 4 with Mathlib. To use:

```bash
# Install Lean 4 and create a project
lake new collatz_cycles
cd collatz_cycles

# Add Mathlib dependency to lakefile.lean
# Copy these .lean files to the project

# Build
lake build
```

## Key Insights Formalized

1. **The Closure Constant C** is bounded below by approximately 0.7·4^k - 3^k for binary cycles
2. **The Denominator Crisis** occurs infinitely often due to Weyl equidistribution
3. **Forced Arithmetic Constraints** make cycles impossible when denominator is small
4. **Growth Bounds** limit how much cycle elements can vary
5. **Tail₂ Structure** creates forced patterns incompatible with cycle closure

While not yet a complete proof, this formalization captures the mathematical framework that strongly suggests no non-trivial binary Collatz cycles exist.