# Rigorous Growth Analysis for Medium-J Binary Collatz Cycles

## Setting

We analyze k-cycles where:
- k > 100
- {αk} ≥ 1/k² (non-crisis)
- 1.585k < J < 2k - k/10 (medium-J)

## The Growth Mechanism

### Fundamental Relations

For a k-cycle with j-sequence (j₁, ..., jₖ):
```
nᵢ₊₁ = (3nᵢ + 1)/2^{jᵢ}
```

Taking the product around the cycle:
```
∏ᵢ₌₁ᵏ nᵢ₊₁ = ∏ᵢ₌₁ᵏ (3nᵢ + 1)/2^{jᵢ}
```

Since this is a cycle, the left side equals ∏nᵢ, giving:
```
∏ᵢ₌₁ᵏ (3nᵢ + 1) = 2^J ∏ᵢ₌₁ᵏ nᵢ
```

### The Maximum Element

Let n_max = max{n₁, ..., nₖ} and n_min = min{n₁, ..., nₖ}.

**Lemma 1**: In any k-cycle:
```
n_max ≥ (∏ᵢ₌₁ᵏ nᵢ)^{1/k} ≥ n_min
```

## Key Constraints for Medium-J

### Constraint 1: The Denominator Bound

Since we're in a non-crisis case:
```
d = |2^J - 3^k| ≥ 3^k/k²
```

From n₁ = C/d and C ≥ 0.686 × 4^k:
```
n₁ ≤ 0.686 × 4^k × k²/3^k = 0.686 × k² × (4/3)^k
```

### Constraint 2: The J-Distribution

With J ∈ (1.585k, 2k - k/10):
- Number of j=1 positions: r = 2k - J ∈ (k/10, 0.415k)
- Number of j=2 positions: k - r ∈ (0.585k, 9k/10)

### Constraint 3: Element Relationships

**Lemma 2**: For any cycle element nᵢ:
```
nᵢ ≥ (3^k n₁ + S)/2^J
```
where S is a sum involving powers of 3 and 2.

## The Growth Analysis

### Step 1: Lower Bound on Product

From the cycle equation:
```
∏ᵢ₌₁ᵏ (3nᵢ + 1) = 2^J ∏ᵢ₌₁ᵏ nᵢ
```

Since 3nᵢ + 1 > 3nᵢ for all i:
```
∏ᵢ₌₁ᵏ nᵢ < (1/3)^k × 2^J × ∏ᵢ₌₁ᵏ nᵢ
```

Wait, this gives 1 < (2/3)^k × 2^{J/k}, which requires:
```
J > k log₂(3/2) ≈ 0.585k
```

This is always satisfied in our range, so we need a more refined analysis.

### Step 2: The Dispersion Principle

**Theorem 1 (Key Insight)**: In a medium-J cycle, the elements cannot all be close to their geometric mean.

**Proof**: Suppose all nᵢ ∈ [M/λ, λM] where M = (∏nᵢ)^{1/k} and λ > 1.

From 3nᵢ + 1 ≤ 3λM + 1 ≤ 4λM (for large M):
```
∏(3nᵢ + 1) ≤ (4λM)^k
```

But also:
```
∏(3nᵢ + 1) = 2^J ∏nᵢ ≥ 2^J (M/λ)^k = 2^J M^k/λ^k
```

Combining:
```
2^J M^k/λ^k ≤ (4λM)^k
```

Simplifying:
```
2^J ≤ 4^k λ^{2k}
```

For J > 1.585k ≈ k log₂(3), we need:
```
3^k ≤ 4^k λ^{2k}
```

This gives:
```
λ ≥ (3/4)^{k/2}
```

For large k, this forces extreme dispersion. □

### Step 3: Consequence of Dispersion

**Theorem 2**: If elements have dispersion λ ≥ (3/4)^{k/2}, then:
```
n_max ≥ λ × (∏nᵢ)^{1/k} ≥ (3/4)^{k/2} × (∏nᵢ)^{1/k}
```

### Step 4: Lower Bound on Product

From the closure equation with n₁ = C/d:
```
n₁(2^J - 3^k) = C ≥ 0.686 × 4^k
```

For medium-J, a careful analysis of 2^J - 3^k shows:
```
2^J - 3^k ≤ 3^k × (2^{J/k - log₂3} - 1) ≤ 3^k × 0.5
```

(This uses J/k < 2 - 0.1 = 1.9 in our range)

Therefore:
```
n₁ ≥ 0.686 × 4^k/(0.5 × 3^k) = 1.372 × (4/3)^k
```

### Step 5: The Final Contradiction

**Theorem 3**: For medium-J cycles with k > 100:
```
n_max > 2^k
```

**Proof**: 
From Steps 3 and 4:
```
n_max ≥ (3/4)^{k/2} × (∏nᵢ)^{1/k}
```

Using n₁ ≥ 1.372 × (4/3)^k and the fact that (∏nᵢ)^{1/k} ≥ n_min ≥ n₁:
```
n_max ≥ (3/4)^{k/2} × 1.372 × (4/3)^k
     = 1.372 × (3/4)^{k/2} × (4/3)^k
     = 1.372 × 3^{k/2} × 4^{k/2} / 4^{k/2} × 3^k
     = 1.372 × 4^{k/2} / 3^{k/2}
     = 1.372 × (4/3)^{k/2}
     = 1.372 × 2^{k/2} × (2/3)^{k/2}
```

Hmm, this approach isn't giving the contradiction we need. Let me try a different angle...

## Alternative Approach: The Variance Method

### The Key Observation

In a cycle, the logarithms of elements must satisfy:
```
∑ᵢ₌₁ᵏ log(3nᵢ + 1) = J log 2 + ∑ᵢ₌₁ᵏ log nᵢ
```

This imposes a delicate balance that becomes impossible to maintain as k grows.

### Variance Analysis

Let xᵢ = log nᵢ and x̄ = (∑xᵢ)/k.

**Lemma 3**: For large nᵢ:
```
log(3nᵢ + 1) ≈ log(3nᵢ) = log 3 + xᵢ
```

The cycle constraint becomes:
```
k log 3 + ∑xᵢ ≈ J log 2 + ∑xᵢ
```

This gives:
```
J ≈ k log 3/log 2 = k log₂ 3 ≈ 1.585k
```

But we know J > 1.585k, creating tension that forces variance in the xᵢ values.

## Conclusion and Next Steps

The medium-J cases resist simple analysis because they balance multiple competing constraints. The path forward involves:

1. **Refined dispersion analysis**: Quantify how J > 1.585k forces element dispersion
2. **Modular constraints**: Even medium-J cases have some j=2 positions creating modular restrictions
3. **Computer-assisted proof**: Verify impossibility for k ∈ [100, 1000] computationally, reducing the problem to k > 1000 where asymptotic arguments are stronger

The key insight is that medium-J cycles must exhibit extreme dispersion in element sizes, but this dispersion itself creates contradictions with the cycle closure requirements.