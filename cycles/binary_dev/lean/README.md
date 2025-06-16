# Lean Formalization of Binary Collatz Cycles Impossibility

This directory contains the Lean 4 formalization of the proof that binary Collatz cycles cannot exist.

## Directory Structure

### BinaryCycles/ - Main Proof (Active)
Contains only the files necessary for the complete proof:

- **Core/Definitions.lean** - Fundamental definitions and basic properties
- **ClosureConstant/Bounds.lean** - Proof that C ≥ 0.686 × 4^k
- **DenominatorCrisis/Crisis.lean** - Crisis analysis and contradiction
- **SmallKVerification.lean** - Computational verification for k ≤ 1000
- **FinalTheorem.lean** - Main theorem combining all cases

### Explorations/ - Development Work (Archived)
Contains exploratory work and alternative approaches:

- **DetailedAttempts/** - Earlier detailed proof attempts
- **Experiments/** - Standalone experiments and templates
- **MediumJ/** - Medium-J case analysis (not yet integrated)
- **ModularConstraints/** - High-J modular analysis (not yet integrated)

### GeneralCycles/ - Future Work
Placeholder for general Collatz cycles where j can take any positive integer value.

## Building

To build the main theorem:

```bash
lake build BinaryCycles.FinalTheorem
```

## Key Results

The main theorem proves:
```lean
theorem binary_collatz_cycles_impossible :
    ∀ k : ℕ, 0 < k → ¬∃ c : BinaryCycle k, True
```

This is established through case analysis:
- Small k (≤ 1000): Computational verification
- Crisis k: Denominator forces n₁ > k² × 2^k, contradicting n₁ ≤ 2^k
- High-J k: Modular incompatibility (to be completed)
- Medium-J k: Structural impossibility (to be completed)

## Current Status

The proof structure is complete but contains `sorry` placeholders:
- Core definitions: 4 sorries (computational lemmas)
- Closure constant bounds: 3 sorries (computational verification)
- Crisis analysis: 5 sorries (technical approximation lemmas)
- Small k verification: 2 sorries (computational verification)
- Final theorem: 2 sorries (high-J and medium-J cases)

**Total: 30 sorries remaining in the main proof files** (down from 62)

## Development Methodology

Following the hybrid approach outlined in CLAUDE.md:
1. Explore phenomena in text/computation
2. Formalize definitions in Lean immediately
3. Verify each proof step formally
4. No proof is complete until Lean accepts it