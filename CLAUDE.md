# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository contains research code for analyzing the Collatz conjecture, specifically focusing on proving the non-existence of non-trivial cycles. The codebase includes mathematical analysis tools for studying binary Collatz cycles, closure constants, and denominator crisis phenomena.

## Key Commands

### Building and Running C Programs

**C.c** - Analyzes the Collatz Closure Constant:
```bash
gcc -o C C.c -lm
./C > C.txt
```

**collatz_tail.c** - Analyzes tail₂ patterns (requires GMP library):
```bash
# On macOS:
brew install gmp
gcc -o collatz_tail collatz_tail.c -lgmp -I/opt/homebrew/include -L/opt/homebrew/lib

# On Linux:
gcc -o collatz_tail collatz_tail.c -lgmp
./collatz_tail > collatz_tail.txt
```

**ak.c** - Finds critical k values for denominator crisis:
```bash
gcc -o ak ak.c -lm
./ak > ak.txt
```

## Architecture and Key Concepts

### Mathematical Framework
The codebase investigates the Collatz conjecture through several mathematical lenses:

1. **Binary Cycles**: Focus on j-sequences where j ∈ {1,2}, representing the power of 2 in the denominator after applying 3n+1.

2. **Closure Constant C**: For any k-cycle, the equation n₁(2^J - 3^k) = C must hold, where C is bounded by approximately 0.7 · 4^k - 3^k.

3. **Denominator Crisis**: When α = 2 - log₂(3) ≈ 0.415, and {αk} (fractional part) is very small, the denominator d = 3^k(2^δ - 1) becomes tiny, forcing n_min to be impossibly large.

### Code Organization
- **C.c**: Computes minimum values of the Closure Constant C for various k and n₁ configurations using exhaustive search
- **ak.c**: Identifies k values where the denominator crisis occurs using Weyl equidistribution
- **collatz_tail.c**: Uses arbitrary precision arithmetic (GMP) to analyze binary tail patterns in large numbers
- **Markdown files**: Document theoretical framework and proof strategies