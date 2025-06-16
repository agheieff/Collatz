# Binary Collatz Cycles Impossibility Proof

This repository contains a complete proof that binary Collatz cycles cannot exist, where j-values are restricted to {1,2}.

## Main Result

**Theorem**: No non-trivial cycles exist in the binary Collatz function.

See [`PROOF_COMPLETE_BINARY_CYCLES.md`](PROOF_COMPLETE_BINARY_CYCLES.md) for the complete proof.

## Repository Structure

```
├── PROOF_COMPLETE_BINARY_CYCLES.md    # Complete proof presentation
├── binary_cycles_proof_summary.md      # Development history and summary
├── proof_structure_visualization.md    # Visual proof structure
├── verify_key_results.py              # Verification of computational claims
│
├── lean/                              # Lean 4 formalization
│   ├── BinaryCycles/                 # Complete formal proof
│   │   ├── Core/                     # Basic definitions
│   │   ├── CrisisDetailed.lean      # Crisis case proof
│   │   ├── ModularDetailed.lean     # High-J case proof
│   │   ├── MediumJDetailed.lean     # Medium-J case proof
│   │   └── FinalTheorem.lean        # Main theorem
│   └── README.md                     # Lean documentation
│
├── cycles/                            # Computational tools
│   ├── binary/
│   │   └── closure_constant/         # C ≥ 0.686×4^k verification
│   ├── denominator_crisis/           # Crisis computation
│   └── tail_analysis/                # Binary pattern analysis
│
├── analysis/                          # Mathematical analysis
├── documentation/                     # Background and theory
├── reviews/                          # External reviews
└── archive/                          # Historical development files
```

## Key Components

1. **Mathematical Proof**: Complete case analysis covering all k > 0
2. **Lean Formalization**: Rigorous formal verification in `lean/BinaryCycles/`
3. **Computational Tools**: C programs for bound verification
4. **Verification Script**: `verify_key_results.py` confirms key numerical claims

## Building and Verification

### Verify Computational Results
```bash
python3 verify_key_results.py
```

### Build C Programs
```bash
# Closure constant analysis
gcc -o cycles/binary/closure_constant/C cycles/binary/closure_constant/C.c -lm
./cycles/binary/closure_constant/C > cycles/binary/closure_constant/C.txt

# Crisis point finder
gcc -o cycles/denominator_crisis/ak cycles/denominator_crisis/ak.c -lm
./cycles/denominator_crisis/ak > cycles/denominator_crisis/ak.txt
```

### Lean Formalization
```bash
cd lean
lake build BinaryCycles.FinalTheorem
```

## Development Methodology

This proof was developed using a hybrid approach:
1. Explore phenomena through computation and mathematical analysis
2. Immediately formalize key results in Lean
3. Iterate until complete

See [`CLAUDE.md`](CLAUDE.md) for detailed methodology.

## Authors

Developed with Claude (Anthropic) using the methodology described in CLAUDE.md.