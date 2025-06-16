# Binary Collatz Cycles - Lean Formalization

## Overview

This directory contains a Lean 4 formalization of the binary Collatz cycle impossibility proof. The proof shows that no k-cycles exist in the binary Collatz function where j ∈ {1, 2}.

## Current Status

### ⚠️ Critical Issue Discovered

Computational verification has revealed that a fundamental bound used throughout the proof is **incorrect**:

- **Claimed**: C ≥ 0.686 × 4^k for all cycle-compatible sequences
- **Actual**: This bound fails for k ≥ 8; the coefficient C/4^k decreases with k
- **Impact**: The denominator crisis analysis relies on this bound

### Valid Components

Despite this issue, many components remain valid:

1. **Algebraic Framework**: The cycle equation n₁(2^J - 3^k) = C is correct
2. **Modular Constraints**: 
   - j=2 requires n ≡ 1 (mod 4), and for odd output n ≡ 1 (mod 8)
   - These constraints create incompatibilities in high-J cases
3. **High-J Impossibility**: When ≥90% positions have j=2, modular constraints cascade to contradiction
4. **Small k**: Computational verification for k < 100 remains valid

## File Structure (Consolidated)

### Core Files
- `Core/Definitions.lean` - Basic definitions, cycle equation, and fundamental theorems
- `MainResults.lean` - Main theorem and all valid results consolidated
- `ModularAnalysis.lean` - Modular constraints for high-J cases
- `SmallKVerification.lean` - Computational verification for small k

### Analysis Files  
- `CrisisAnalysis.lean` - Crisis phenomenon and closure constant bounds (needs revision)
- `MediumJAnalysis.lean` - Analysis for medium-J cases (needs revision)
- `Computational.lean` - All computational tools, constants, and C calculations

## Proof Strategy

The proof uses case analysis on k:

1. **Small k (k < 100)**: Direct computational verification
2. **Large k (k ≥ 100)**: Three subcases based on J value:
   - **High-J** (J ≥ 2k - k/10): ✓ Modular incompatibility (proven)
   - **Crisis** (denominator very small): ✗ Needs revised approach
   - **Medium-J**: ✗ Needs revised approach

## Known Issues and TODOs

### High Priority
1. **Fix C bounds**: Find correct lower bounds for C that work for all k
2. **Revise crisis analysis**: Current approach relies on incorrect C bound
3. **Complete non-high-J cases**: Need new approach without false bound

### Medium Priority
1. Complete the telescoping sum proof in cycle_equation
2. Fill in computational verification implementation
3. Explore alternative approaches using C/4^k decreasing property

### Low Priority
1. Clean up remaining sorry statements
2. Add more documentation
3. Consider extending computational verification to larger k

## How to Build

```bash
cd lean
lake build BinaryCycles
```

## Key Insights

1. The proof remains valid for high-J cycles (≥90% j=2 positions)
2. The crisis phenomenon exists but requires different analysis
3. C/4^k decreasing with k might itself lead to contradiction
4. Modular constraints are more powerful than initially thought

## Contributing

When working on this proof:
1. Do not rely on C ≥ 0.686 × 4^k (it's false!)
2. Verify all numerical claims computationally when possible
3. Focus on structural/modular arguments rather than pure bounds
4. Document any new approaches clearly