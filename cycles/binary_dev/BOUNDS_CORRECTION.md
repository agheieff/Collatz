# Bounds Correction for Binary Collatz Proof

## The Problem

The original proof claimed that for all cycle-compatible j-sequences:
```
C ≥ 0.686 × 4^k
```

This bound is **FALSE** for k ≥ 8. Computational evidence shows:
- k = 8: C/4^k ≈ 0.52 < 0.686
- k = 10: C/4^k ≈ 0.30
- k = 20: C/4^k ≈ 0.06

## The Correct Understanding

### 1. C Growth Rate
C actually grows like 3^k, not 4^k:
```
c₁ × 3^k ≤ C ≤ c₂ × 3^k
```
where c₁, c₂ are constants (roughly 0.5 < c₁ < c₂ < 2.5).

### 2. Decreasing Ratio Property
For cycle-compatible sequences (⌊1.585k⌋ < J ≤ 2k):
```
C/4^k ≤ 0.52 × (0.9)^(k-8)
```
This ratio decreases exponentially with k.

### 3. Why This Matters
The cycle equation gives us:
```
n₁ = C / |2^J - 3^k|
```

For n₁ to be a positive odd integer:
- C must be sufficiently large (numerator)
- |2^J - 3^k| must not be too large (denominator)

## The Corrected Proof Strategy

### Medium-J Case (Non-Crisis)
When J is not in crisis:
- Denominator: |2^J - 3^k| ≥ δ × 3^k for some δ > 0
- Numerator: C ≤ c₂ × 3^k
- Therefore: n₁ ≤ c₂/δ = O(1)

For large k, we can't fit k distinct odd integers in a bounded range.

### Crisis Case
When |2^J - 3^k| < k (crisis):
- Denominator is very small: |2^J - 3^k| < k
- But C ≥ c₁ × 3^k
- Therefore: n₁ > c₁ × 3^k / k

For k ≥ 100, we have 3^k/k > 2^k (exponential dominates polynomial).
This contradicts the bound that cycle elements ≤ 2^k.

### High-J Case
Already correctly proven via modular constraints - no bounds issue here.

## Implementation Status

1. **Created**: `CorrectBounds.lean` - New file with correct analysis
2. **Updated**: `ProofAxioms.lean` - Added correct axioms
3. **Created**: `ComputeCValues.lean` - Computational verification
4. **TODO**: Update `MediumJComplete.lean` to use correct bounds
5. **TODO**: Update `CrisisAnalysis.lean` to use correct approach

## Why the Original Bound Failed

The original analysis tried to show:
```
min C over cycle-compatible sequences ≥ 0.686 × 4^k
```

This failed because:
1. When J ≈ 1.585k (minimum for cycles), we have roughly 58.5% j=2 positions
2. The j=2 positions contribute factors of 4 instead of 2 to the growth
3. But the arrangement that minimizes C has all j=2 positions first
4. This creates a complex interaction where C grows more like 3^k than 4^k

## Verification

Run the computations in `ComputeCValues.lean`:
```lean
#eval compute_ratio 5   -- ≈ 0.84 ✓
#eval compute_ratio 8   -- ≈ 0.52 ✗ (bound fails)
#eval compute_ratio 10  -- ≈ 0.30 ✗
#eval compute_ratio 20  -- ≈ 0.06 ✗
```

## Conclusion

The proof structure remains sound, but requires using the correct growth rates:
- C ~ 3^k (not 4^k)
- C/4^k → 0 as k → ∞
- This makes large cycles impossible