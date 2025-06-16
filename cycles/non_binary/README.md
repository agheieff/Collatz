# Non-Binary Collatz Cycles

This directory is for exploring Collatz cycles where j can take values beyond {1, 2}.

## Potential Extensions

### 1. j ∈ {1, 2, 3}
- Adds the possibility of dividing by 8
- More complex modular constraints
- Larger search space

### 2. General j ∈ {1, 2, ..., m}
- Arbitrary maximum division
- Requires generalized analysis techniques

### 3. Variable j bounds
- j_max depends on n or position in cycle
- Dynamic constraints

## Framework Structure (TODO)

```
non_binary/
├── definitions/      # Generalized definitions
├── constraints/      # Extended modular analysis
├── computational/    # Search algorithms
└── proofs/          # Impossibility proofs
```

## Key Questions

1. Do the same techniques (modular constraints, growth analysis) generalize?
2. What new phenomena emerge with larger j values?
3. Are there critical j values where behavior changes qualitatively?

## Related Work

The binary case (j ∈ {1, 2}) is now complete. This provides a foundation for:
- Understanding which proof techniques generalize
- Identifying new challenges with larger j
- Developing computational search strategies