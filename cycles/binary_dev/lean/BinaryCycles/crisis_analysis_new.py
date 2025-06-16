#!/usr/bin/env python3
"""
Analyze what actually happens during crisis cases.
We know the denominator |2^J - 3^k| is tiny, but what about C?
"""

import math

def analyze_crisis_C(k: int):
    """
    During crisis, J ≈ k × log₂(3) ≈ 1.585k
    What happens to C for these specific J values?
    """
    log2_3 = math.log(3) / math.log(2)  # ≈ 1.585
    
    print(f"\nCrisis analysis for k = {k}")
    print("-" * 50)
    
    # Crisis J values are very close to k × log₂(3)
    J_exact = k * log2_3
    J_candidates = [math.floor(J_exact), math.ceil(J_exact)]
    
    for J in J_candidates:
        if J <= k or J > 2 * k:
            continue
            
        # Denominator during crisis
        d = abs(2**J - 3**k)
        ratio = 2**J / 3**k
        
        print(f"\nJ = {J} (J/k = {J/k:.4f}):")
        print(f"  2^J/3^k = {ratio:.8f}")
        print(f"  |2^J - 3^k| = {d}")
        
        # For crisis J values, what's special about C?
        # C depends on the j-pattern
        
        # Pattern 1: All j=2 until forced to use j=1
        j2_count = J - k
        j1_count = k - j2_count
        print(f"  Pattern: {j2_count} × j=2, {j1_count} × j=1")
        
        # Rough C estimate for this pattern
        # When j=2 comes first: C ≈ 3^k + lower order terms
        C_approx = 3**k * (1 + 2**(J-k))
        
        print(f"  C ≈ {C_approx:.2e}")
        print(f"  C/4^k ≈ {C_approx/4**k:.4f}")
        print(f"  n₁ = C/d ≈ {C_approx/d:.2e}")
        
        # Check if n₁ could be reasonable
        if C_approx/d < 2**k:
            print(f"  Potentially feasible (n₁ < 2^k)")
        else:
            print(f"  Too large (n₁ > 2^k = {2**k})")

def find_crisis_points(max_k: int = 50):
    """Find k values where crisis occurs."""
    log2_3 = math.log(3) / math.log(2)
    
    print("Crisis points (where {k × log₂(3)} is tiny):")
    print("-" * 50)
    
    crisis_points = []
    
    for k in range(2, max_k + 1):
        fractional_part = (k * log2_3) % 1
        
        # Crisis when fractional part is very close to 0 or 1
        # Need to be more generous with the threshold to find examples
        if fractional_part < 0.1 or fractional_part > 0.9:
            crisis_points.append(k)
            J = round(k * log2_3)
            d = abs(2**J - 3**k)
            print(f"k = {k}: {k}×log₂(3) = {k * log2_3:.4f} ≈ {J}")
            print(f"  |2^{J} - 3^{k}| = {d}")
    
    return crisis_points

def deep_crisis_analysis(k: int):
    """Detailed analysis of a specific crisis case."""
    log2_3 = math.log(3) / math.log(2)
    J = round(k * log2_3)
    
    print(f"\nDeep analysis of crisis at k = {k}, J = {J}")
    print("=" * 60)
    
    # During crisis, we need to understand:
    # 1. The exact value of C for different j-patterns
    # 2. Whether any pattern gives feasible n₁
    
    d = abs(2**J - 3**k)
    print(f"Denominator: |2^{J} - 3^{k}| = {d}")
    
    # Check different j-patterns
    print("\nChecking j-patterns:")
    
    # Pattern 1: j=2 as much as possible
    j2_max = J - k
    j1_min = k - j2_max
    
    print(f"\n1. Maximum j=2 pattern: {j2_max}×j=2, {j1_min}×j=1")
    # For this pattern, C is minimized
    # C ≈ 3^k when j=2 dominates
    C_min = 3**k
    n1_min = C_min / d
    print(f"   C ≈ {C_min:.2e}, n₁ ≈ {n1_min:.2e}")
    
    # Pattern 2: j=1 as much as possible (but still need J total)
    # This gives larger C but same denominator
    print(f"\n2. More j=1 pattern analysis...")
    # C grows when we use more j=1 early
    
    # The key question: Is there ANY j-pattern where:
    # - J is correct (sum of j values)
    # - n₁ = C/d is a reasonable odd integer
    # - All modular constraints are satisfied

def main():
    """Main crisis analysis."""
    print("Crisis Analysis for Binary Collatz Cycles")
    print("=" * 60)
    
    # Find crisis points
    crisis_k = find_crisis_points(30)
    
    print(f"\nFound {len(crisis_k)} crisis points in k ≤ 30")
    
    # Analyze first few crisis cases
    print("\n" + "=" * 60)
    for k in crisis_k[:3]:
        analyze_crisis_C(k)
    
    # Deep dive on specific case
    if crisis_k:
        print("\n" + "=" * 60)
        deep_crisis_analysis(crisis_k[0])
    
    print("\n" + "=" * 60)
    print("Key insight: Even during crisis when denominator is tiny,")
    print("the constraints on j-patterns and modular arithmetic")
    print("still make cycles extremely unlikely.")

if __name__ == "__main__":
    main()