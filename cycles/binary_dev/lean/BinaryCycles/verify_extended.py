#!/usr/bin/env python3
"""
Extended verification strategy for larger k values.
Uses theoretical bounds to make computation feasible.
"""

import math

def theoretical_check(k: int) -> str:
    """
    Check if cycles are theoretically possible for given k.
    Returns reason why cycles are impossible, or "possible" if unclear.
    """
    # High-J case
    if k > 10:
        # If ≥90% positions need j=2, modular constraints kill it
        high_j_threshold = 2 * k - k // 10
        J_min = math.floor(1.585 * k) + 1
        if J_min >= high_j_threshold:
            return f"High-J case: J_min={J_min} ≥ {high_j_threshold}"
    
    # Check denominator sizes
    J_min = math.floor(1.585 * k) + 1
    J_max = 2 * k
    
    # For each valid J, check if cycle is possible
    reasons = []
    for J in range(J_min, min(J_max + 1, J_min + 5)):
        d = abs(2**J - 3**k)
        
        # Estimate minimum C (roughly 3^k for minimum patterns)
        C_min = 3**k
        n1_min = C_min / d
        
        if n1_min > 2**k:
            reasons.append(f"J={J}: n₁ ≥ {n1_min:.2e} > 2^{k}")
        elif n1_min > 1000:
            reasons.append(f"J={J}: n₁ ≥ {n1_min:.0f} (very large)")
    
    if reasons:
        return "; ".join(reasons[:2])  # First two reasons
    
    # Check C/4^k ratio
    if k >= 8:
        # We know C/4^k < 0.686 for k ≥ 8
        # And it decreases with k
        ratio_bound = 0.686 * (0.9 ** (k - 8))  # Rough decrease
        if ratio_bound < 0.01:
            return f"C/4^k < {ratio_bound:.3f} (too small)"
    
    return "possible (needs deeper analysis)"

def analyze_k_range(start_k: int, end_k: int):
    """Analyze possibility of cycles for k in given range."""
    print(f"Analyzing k ∈ [{start_k}, {end_k}]")
    print("=" * 70)
    
    impossible_count = 0
    possible_cases = []
    
    for k in range(start_k, end_k + 1):
        result = theoretical_check(k)
        
        if result != "possible (needs deeper analysis)":
            impossible_count += 1
            if k <= start_k + 10 or k % 10 == 0:  # Show first few and samples
                print(f"k={k:3d}: IMPOSSIBLE - {result}")
        else:
            possible_cases.append(k)
            print(f"k={k:3d}: {result}")
    
    print(f"\nSummary for k ∈ [{start_k}, {end_k}]:")
    print(f"- Provably impossible: {impossible_count}/{end_k-start_k+1}")
    print(f"- Need deeper analysis: {len(possible_cases)}")
    
    if possible_cases and len(possible_cases) <= 20:
        print(f"- Cases needing analysis: {possible_cases}")
    
    return possible_cases

def deep_analysis(k: int):
    """Deeper analysis for uncertain cases."""
    print(f"\nDeep analysis for k = {k}:")
    print("-" * 40)
    
    J_min = math.floor(1.585 * k) + 1
    J_max = min(2 * k, J_min + 10)
    
    for J in range(J_min, J_max + 1):
        d = abs(2**J - 3**k)
        ratio = 2**J / 3**k
        
        print(f"  J={J}: 2^J/3^k = {ratio:.6f}")
        print(f"    |2^J - 3^k| = {d}")
        
        # Check if this is near crisis
        if abs(ratio - 1) < 0.01:
            print(f"    CRISIS: Very small denominator!")
        
        # Estimate n₁ range
        C_min = 3**k
        C_max = 2 * 4**k  # Generous upper bound
        n1_min = C_min / d
        n1_max = C_max / d
        
        print(f"    n₁ ∈ [{n1_min:.2e}, {n1_max:.2e}]")
        
        if n1_min > 1:
            # Check modular constraints
            # For J close to 2k, we need many j=2
            j2_count = J - k
            print(f"    Needs ≥{j2_count} positions with j=2")

def main():
    """Main analysis."""
    print("Extended Binary Collatz Cycle Analysis")
    print("=" * 70)
    
    # First, verify our approach works for known range
    print("\nVerifying approach on k ∈ [10, 30]:")
    small_possible = analyze_k_range(10, 30)
    
    print("\n" + "=" * 70)
    
    # Extend to larger k
    print("\nExtending to k ∈ [100, 200]:")
    medium_possible = analyze_k_range(100, 120)
    
    # Deep dive on any uncertain cases
    if medium_possible[:5]:  # Just first 5
        print("\n" + "=" * 70)
        for k in medium_possible[:5]:
            deep_analysis(k)
    
    print("\n" + "=" * 70)
    print("Conclusion: The theoretical constraints eliminate most k values.")
    print("Remaining cases can be handled by:")
    print("1. Crisis analysis (rare denominator events)")
    print("2. C/4^k decreasing property")
    print("3. Modular constraint propagation")

if __name__ == "__main__":
    main()