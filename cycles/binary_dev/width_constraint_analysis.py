#!/usr/bin/env python3
"""
Analyze the width constraint for medium-J cycles to refine it for smaller k.

Key insight: For medium-J cycles, elements are bounded but need to be distinct odd integers.
"""

import math
from typing import Tuple, List

def analyze_element_bounds(k: int, J: int) -> Tuple[float, float]:
    """
    Analyze bounds on cycle elements for given k and J.
    Returns (lower_bound_ratio, upper_bound_ratio) for elements relative to n1.
    """
    # For medium-J: floor(1.585*k) < J < 2k - k/10
    # Number of j=2 positions
    num_j2 = J - k
    num_j1 = k - num_j2
    
    # Growth factors through the cycle
    # j=1: multiply by 3/2
    # j=2: multiply by 3/4
    
    # Maximum growth: all j=1 first
    max_ratio = (3/2)**num_j1 * (3/4)**num_j2
    
    # Minimum growth: all j=2 first  
    min_ratio = (3/4)**num_j2 * (3/2)**num_j1
    
    # But we need to return back to n1, so product = 1
    # This means actual bounds are tighter
    
    # For a cycle, the product of all ratios must equal 1
    # (3/2)^(#j=1) * (3/4)^(#j=2) = (3/2)^k * 2^(-J) = 3^k / 2^J
    
    # Since 2^J ≈ 3^k (within factor δ), ratios cluster near 1
    
    return min_ratio, max_ratio

def count_odd_in_range(lower: float, upper: float) -> int:
    """Count odd integers in range [lower, upper]."""
    # First odd ≥ lower
    first_odd = int(lower)
    if first_odd % 2 == 0:
        first_odd += 1
    if first_odd < lower:
        first_odd += 2
    
    # Last odd ≤ upper
    last_odd = int(upper)
    if last_odd % 2 == 0:
        last_odd -= 1
    
    if first_odd > last_odd:
        return 0
    
    return (last_odd - first_odd) // 2 + 1

def analyze_width_constraint(k_values: List[int]):
    """Analyze when width constraint becomes effective."""
    
    print("=== Width Constraint Analysis ===\n")
    
    for k in k_values:
        print(f"\n--- k = {k} ---")
        
        # Medium-J range
        J_min = math.floor(1.585 * k) + 1
        J_max = 2 * k - k // 10 - 1
        
        print(f"Medium-J range: {J_min} ≤ J ≤ {J_max}")
        
        # Analyze for middle of medium-J range
        J_mid = (J_min + J_max) // 2
        num_j2 = J_mid - k
        
        print(f"Mid-range J = {J_mid}, #j=2 = {num_j2}")
        
        # Key insight: In medium-J, elements cluster around n1
        # Due to cycle constraint: n1 * (2^J - 3^k) = C
        
        # C bounds (from computational evidence)
        C_lower = 0.1 * 3**k  # Conservative lower bound
        C_upper = 0.9 * 3**k  # Conservative upper bound
        
        # Denominator for medium-J non-crisis
        # |2^J - 3^k| ≈ δ * 3^k where δ depends on fractional part of k*log2(3)
        # For non-crisis, δ ≥ 1/k² typically
        
        delta_min = 1 / k**2
        delta_typical = 0.01  # More typical value
        
        denom_lower = delta_min * 3**k
        denom_typical = delta_typical * 3**k
        
        # n1 bounds
        n1_max_tight = C_upper / denom_lower
        n1_max_typical = C_upper / denom_typical
        
        print(f"\nn1 bounds:")
        print(f"  Tight bound: n1 ≤ {C_upper}/{denom_lower:.2e} = {n1_max_tight:.2e}")
        print(f"  Typical: n1 ≤ {C_upper}/{denom_typical:.2e} = {n1_max_typical:.2e}")
        
        # Element distribution
        # Elements stay within constant factor of n1
        # Conservative: elements in range [n1/10, 10*n1]
        
        factor = 10
        if n1_max_typical < float('inf'):
            range_lower = n1_max_typical / factor
            range_upper = n1_max_typical * factor
            
            num_odd = count_odd_in_range(range_lower, range_upper)
            
            print(f"\nElement range: [{range_lower:.2e}, {range_upper:.2e}]")
            print(f"Number of odd integers in range: {num_odd}")
            print(f"Need k = {k} distinct odd integers")
            
            if num_odd < k:
                print(f"*** CONTRADICTION: Not enough odd integers! ***")
            else:
                print(f"Ratio: {num_odd/k:.2f}x more odd integers than needed")
                
        # More refined analysis
        print(f"\n=== Refined Analysis ===")
        
        # Key observation: In medium-J, growth ratios balance
        # This creates tighter clustering than factor-of-10 estimate
        
        # Analyze actual growth ratios
        min_ratio, max_ratio = analyze_element_bounds(k, J_mid)
        print(f"Growth ratio range: [{min_ratio:.4f}, {max_ratio:.4f}]")
        
        # If all elements must be within factor R of n1
        # Then width ≤ n1 * R
        # Number of odd integers ≤ n1 * R / 2
        
        # But need k distinct, so n1 * R / 2 ≥ k
        # This gives n1 ≥ 2k/R
        
        # However, n1 ≤ C/denominator ≈ constant
        # Contradiction when 2k/R > constant

def analyze_j_pattern_constraints(k: int):
    """Analyze constraints from j-pattern structure."""
    
    print(f"\n=== J-Pattern Constraints for k = {k} ===")
    
    # In medium-J, we have mixed j=1 and j=2
    J_min = math.floor(1.585 * k) + 1
    J_max = 2 * k - k // 10 - 1
    
    # Key constraint: j=2 positions must have n ≡ 1 (mod 4)
    # This creates modular sieving
    
    print(f"\nModular constraints:")
    print(f"- j=2 requires n ≡ 1 (mod 4)")
    print(f"- j=1 works for any odd n")
    
    # Analyze for typical medium-J
    J_mid = (J_min + J_max) // 2
    num_j2 = J_mid - k
    
    print(f"\nFor J = {J_mid}:")
    print(f"- Need {num_j2} positions with n ≡ 1 (mod 4)")
    print(f"- Need {k - num_j2} positions with any odd n")
    
    # This creates additional structure we can exploit
    
    # In a range of width W, we have:
    # - W/2 odd numbers total
    # - W/4 numbers ≡ 1 (mod 4)
    # - W/4 numbers ≡ 3 (mod 4)
    
    print(f"\nWidth analysis with modular constraints:")
    print(f"Need at least {num_j2} numbers ≡ 1 (mod 4)")
    print(f"This requires width W ≥ {4 * num_j2}")
    print(f"But total width must contain {k} distinct odd integers")
    print(f"This requires width W ≥ {2 * k}")
    
    # The tighter constraint
    min_width = max(4 * num_j2, 2 * k)
    print(f"\nMinimum width required: {min_width}")

def explore_density_argument(k_values: List[int]):
    """Explore density-based contradiction."""
    
    print("\n=== Density-Based Analysis ===")
    
    for k in k_values:
        # Key idea: Elements must be "well-separated" due to Collatz dynamics
        # Adjacent elements can't be too close
        
        print(f"\n--- k = {k} ---")
        
        # Minimum separation between consecutive odd integers in a cycle
        # Due to 3n+1 operation, if n1 and n2 are close, their images diverge
        
        # Conservative estimate: elements separated by at least their value / k
        # (This comes from growth factor analysis)
        
        # If n_min is smallest element, need room for k elements
        # each separated by ≥ n_min/k
        # Total width ≥ n_min + (k-1) * n_min/k = n_min * (1 + (k-1)/k) ≈ 2*n_min
        
        # But from cycle equation: n_min ≥ n1/factor ≈ constant/factor
        
        print("Element separation analysis:")
        print(f"- Need k = {k} distinct odd integers")
        print(f"- Minimum separation ≈ n_min/{k}")
        print(f"- Total width ≈ 2*n_min")
        print(f"- But n_min bounded by constant (from n1 bound)")
        
        # Critical k where contradiction occurs
        # When k > width/min_separation
        
        # Rough estimate
        typical_n1_bound = 1000  # From C/denominator analysis
        typical_width = 10 * typical_n1_bound
        min_separation = 2  # At least 2 between odd integers
        
        max_elements = typical_width // min_separation
        
        print(f"\nRough density limit:")
        print(f"- Typical n1 bound: {typical_n1_bound}")
        print(f"- Typical width: {typical_width}")
        print(f"- Maximum elements: {max_elements}")
        
        if k > max_elements:
            print(f"*** CONTRADICTION: k = {k} > {max_elements} ***")

def main():
    """Run all analyses."""
    
    # Key k values to analyze
    k_values = [500, 750, 1000, 2000, 5000, 10000]
    
    # Width constraint analysis
    analyze_width_constraint(k_values)
    
    # J-pattern constraints
    print("\n" + "="*60 + "\n")
    for k in [500, 1000, 2000]:
        analyze_j_pattern_constraints(k)
    
    # Density arguments
    print("\n" + "="*60 + "\n")
    explore_density_argument(k_values)
    
    # Summary
    print("\n" + "="*60)
    print("\n=== Summary: Paths to Close the Gap ===")
    print("\n1. Refined Width Constraint:")
    print("   - Current: Works for k > 10000")
    print("   - Goal: Reduce to k > 1000")
    print("   - Key: Tighter bounds on element distribution")
    
    print("\n2. Modular Sieving:")
    print("   - j=2 positions need n ≡ 1 (mod 4)")
    print("   - Creates additional constraints on element placement")
    print("   - Combine with width analysis")
    
    print("\n3. Density + Separation:")
    print("   - Elements can't be arbitrarily close")
    print("   - Minimum separation from Collatz dynamics")
    print("   - May give contradiction for k > 1000")
    
    print("\n4. J-Pattern Impossibility:")
    print("   - Certain j-patterns may be impossible")
    print("   - Would reduce search space dramatically")
    print("   - Focus on patterns incompatible with bounded elements")

if __name__ == "__main__":
    main()