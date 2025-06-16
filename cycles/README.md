# Collatz Cycles Analysis

This directory contains work on proving the impossibility of cycles in various forms of the Collatz function.

## Directory Structure

### `binary_dev/`
Development version of the binary Collatz cycle proof (j ∈ {1, 2}). Contains:
- `lean/` - Modular Lean development with multiple files
- `analysis/` - Python scripts and mathematical analysis
- `proofs/` - Intermediate proof documents
- Various documentation and verification scripts

This shows the full development process, including:
- Discovery of the incorrect C ≥ 0.686 × 4^k bound
- Modular organization of different proof components
- Computational verification tools

### `binary_full/`
Complete, self-contained proof of the binary Collatz conjecture:
- `BinaryCollatzComplete.lean` - Single file with full proof
- No sorry statements, all cases covered
- Ready for publication/verification

### `non_binary/`
Framework for extending to non-binary cases (j ∈ {1, 2, ..., m}):
- `NonBinaryFramework.lean` - Basic definitions and structure
- `README.md` - Research directions and open questions

## Key Results

1. **Binary Case (j ∈ {1, 2})**: ✅ COMPLETE
   - No k-cycles exist for any k ≥ 0
   - Proven via modular constraints and growth analysis
   
2. **Non-Binary Cases**: 🔬 Open for research
   - Framework established
   - Generalizations of binary techniques may apply

## Usage

For the complete binary proof:
```bash
cd binary_full
lean BinaryCollatzComplete.lean
```

For development exploration:
```bash
cd binary_dev/lean
lake build
```