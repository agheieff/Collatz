# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository contains research code for analyzing the Collatz conjecture, specifically focusing on proving the non-existence of non-trivial cycles. The codebase includes mathematical analysis tools for studying binary Collatz cycles, closure constants, and denominator crisis phenomena.

## Key Commands

### Building and Running C Programs

**cycles/binary/closure_constant/C.c** - Analyzes the Collatz Closure Constant:
```bash
gcc -o cycles/binary/closure_constant/C cycles/binary/closure_constant/C.c -lm
./cycles/binary/closure_constant/C > cycles/binary/closure_constant/C.txt
```

**cycles/tail_analysis/collatz_tail.c** - Analyzes tail₂ patterns (requires GMP library):
```bash
# On macOS:
brew install gmp
gcc -o cycles/tail_analysis/collatz_tail cycles/tail_analysis/collatz_tail.c -lgmp -I/opt/homebrew/include -L/opt/homebrew/lib

# On Linux:
gcc -o cycles/tail_analysis/collatz_tail cycles/tail_analysis/collatz_tail.c -lgmp
./cycles/tail_analysis/collatz_tail > cycles/tail_analysis/collatz_tail.txt
```

**cycles/denominator_crisis/ak.c** - Finds critical k values for denominator crisis:
```bash
gcc -o cycles/denominator_crisis/ak cycles/denominator_crisis/ak.c -lm
./cycles/denominator_crisis/ak > cycles/denominator_crisis/ak.txt
```

**bounds/rigorous_bound.c** - Computes rigorous bounds:
```bash
gcc -o bounds/rigorous_bound bounds/rigorous_bound.c -lm
./bounds/rigorous_bound > bounds/rigorous_bound_results.txt
```

## Proof Development Methodology

### Hybrid Approach: Text Exploration + Lean Verification

When developing mathematical proofs in this repository, follow this methodology:

1. **Explore** ideas and phenomena using natural language and computational experiments
2. **Formalize** key definitions in Lean immediately after discovering them
3. **Sketch** proof strategies in text/markdown
4. **Verify** each proof step in Lean before claiming completion
5. **Iterate** between informal exploration and formal verification

**Important**: No proof should be considered complete until it has been formalized and checked in Lean. The text/markdown files serve as motivation and explanation, while Lean files provide the rigorous verification.

### Critical Reminders for Proof Development

When working on mathematical proofs in this repository, please be aware of common pitfalls:

1. **Avoid unjustified assumptions** - Don't assume elements are separated by specific amounts (like 2√k) without proof
2. **Be rigorous with "sorry" statements** - Each one represents a gap that might be unfillable  
3. **Don't claim near-completion prematurely** - The Collatz conjecture is unsolved for good reasons
4. **Focus on what's actually proven** - Distinguish clearly between proven facts and hopeful assumptions
5. **Watch for circular reasoning** - Especially in bounds and constraint arguments

Common traps to avoid:
- Assuming element separation without deriving it from dynamics
- Pulling constants from thin air (e.g., "width ≤ 5000 because n₁ ~ 50")
- Making counting arguments without proper justification
- Claiming contradictions based on unproven bounds
- Getting carried away with "this should work" arguments

Remember: If elementary arguments could solve this, it would have been solved decades ago. Be skeptical of "simple" approaches and maintain mathematical rigor throughout.

## Architecture and Key Concepts

### Mathematical Framework
The codebase investigates the Collatz conjecture through several mathematical lenses:

1. **Binary Cycles**: Focus on j-sequences where j ∈ {1,2}, representing the power of 2 in the denominator after applying 3n+1.

2. **Closure Constant C**: For any k-cycle, the equation n₁(2^J - 3^k) = C must hold, where C is bounded by approximately 0.7 · 4^k - 3^k.

3. **Denominator Crisis**: When α = 2 - log₂(3) ≈ 0.415, and {αk} (fractional part) is very small, the denominator d = 3^k(2^δ - 1) becomes tiny, forcing n_min to be impossibly large.

### Code Organization
- **cycles/binary/closure_constant/**: Contains C.c which computes minimum values of the Closure Constant C for various k and n₁ configurations using exhaustive search
- **cycles/binary/proofs/**: Binary cycle proof documents (binary.md, binary2.md, binary_collatz_cycles_impossibility.md, binary_cycles_proof.md)
- **cycles/denominator_crisis/**: Contains ak.c (identifies critical k values where denominator crisis occurs) and verify_crisis_cycles.c
- **cycles/tail_analysis/**: Contains collatz_tail.c which uses arbitrary precision arithmetic (GMP) to analyze binary tail patterns in large numbers
- **bounds/**: Contains rigorous_bound.c for computing rigorous mathematical bounds
- **documentation/**: General documentation and theoretical framework (alternative_approaches.md, arithmetic_contradiction.md, full.md, modular_constraints_proof.md)
- **reviews/**: External reviews and responses (gemini_review.txt, response_to_gemini_revised_proof.md)
- **lean/**: Lean formal verification files
  - **BinaryCycles/**: Complete formalization of binary cycles impossibility proof
    - Core/: Basic definitions and structures
    - ClosureConstant/: Closure constant bounds proofs
    - DenominatorCrisis/: Crisis analysis and contradictions
    - ModularConstraints/: High-J modular incompatibility
    - MediumJ/: Medium-J structural analysis
    - Main.lean: Unified impossibility theorem
  - **GeneralCycles/**: Work on general Collatz cycles (j ∈ {1,2,...,m})
  - **Experiments/**: Exploratory Lean code and proof attempts