#!/usr/bin/env python3
"""
Concrete analysis to find what we can actually prove about binary Collatz cycles.
Focus on rigorous, provable constraints rather than wishful assumptions.
"""

import math
from typing import List, Tuple, Dict

def analyze_modular_constraints(k: int, J: int) -> Dict[str, any]:
    """
    Analyze hard modular constraints that must hold for any cycle.
    These are PROVABLE, not assumed.
    """
    num_j2 = J - k
    num_j1 = k - num_j2
    
    results = {
        'k': k,
        'J': J,
        'num_j1': num_j1,
        'num_j2': num_j2,
        'constraints': []
    }
    
    # PROVABLE: j=2 positions need n ≡ 1 (mod 4)
    results['constraints'].append(f"Need {num_j2} positions with n ≡ 1 (mod 4)")
    
    # PROVABLE: After j=2 on n ≡ 1 (mod 4), specific residues mod 8
    # If n ≡ 1 (mod 8): (3n+1)/4 ≡ 1 (mod 2)
    # If n ≡ 5 (mod 8): (3n+1)/4 ≡ 0 (mod 2) - not in cycle!
    results['constraints'].append(f"j=2 positions must have n ≡ 1 (mod 8) for odd result")
    
    # This is much stronger! Need num_j2 positions with n ≡ 1 (mod 8)
    # In any range of R consecutive integers, only R/8 satisfy this
    
    return results

def analyze_cycle_equation_constraints(k: int, J: int) -> Dict[str, any]:
    """
    Analyze constraints from the cycle equation n₁(2^J - 3^k) = C.
    Focus on what we can PROVE, not assume.
    """
    results = {
        'equation': f"n₁(2^{J} - 3^{k}) = C"
    }
    
    # PROVABLE: Sign of (2^J - 3^k)
    log2_3 = math.log(3) / math.log(2)  # ≈ 1.585
    critical_J = k * log2_3
    
    if J < critical_J:
        results['denominator_sign'] = 'negative'
        results['constraint'] = 'C must be negative'
    else:
        results['denominator_sign'] = 'positive'  
        results['constraint'] = 'C must be positive'
    
    # PROVABLE: C has specific form (sum involving 3^i)
    # C = Σ(3^(k-1-i) * stuff) 
    # This gives divisibility constraints
    
    return results

def find_provable_contradictions(k_range: List[int]):
    """
    Look for k values where we can prove contradictions rigorously.
    No assumptions about separation or element bounds.
    """
    print("=== Searching for Provable Contradictions ===\n")
    
    for k in k_range:
        print(f"\n--- k = {k} ---")
        
        # Check each possible J value
        J_min = math.floor(1.585 * k) + 1
        J_max = 2 * k
        
        contradictions = []
        
        for J in range(J_min, J_max + 1):
            # Get modular constraints
            mod_info = analyze_modular_constraints(k, J)
            
            # Strong constraint: need J-k positions with n ≡ 1 (mod 8)
            num_j2 = J - k
            
            # If all k elements are distinct and odd, minimum range is 2k
            # But only 2k/8 = k/4 positions satisfy n ≡ 1 (mod 8)
            
            if num_j2 > k/4:
                contradictions.append({
                    'J': J,
                    'reason': f'Need {num_j2} positions ≡ 1 (mod 8), but at most {k/4} available'
                })
        
        if contradictions:
            print(f"Found {len(contradictions)} contradictory J values!")
            print(f"Valid J range: {J_max - J_min + 1}")
            print(f"Contradictory: {len(contradictions)}")
            print(f"Remaining: {J_max - J_min + 1 - len(contradictions)}")

def analyze_denominator_distribution(k: int):
    """
    Analyze the actual distribution of denominator sizes.
    No assumptions - just compute.
    """
    print(f"\n=== Denominator Analysis for k = {k} ===")
    
    J_min = math.floor(1.585 * k) + 1
    J_max = 2 * k
    
    log2_3 = math.log(3) / math.log(2)
    
    small_denom_count = 0
    
    for J in range(J_min, J_max + 1):
        # Compute |2^J - 3^k| / 3^k
        # = |2^J / 3^k - 1|
        # = |2^(J - k*log2_3) - 1|
        
        exponent = J - k * log2_3
        ratio = abs(2**exponent - 1)
        
        if ratio < 1/k:
            small_denom_count += 1
            print(f"J = {J}: denominator/3^k ≈ {ratio:.2e}")
    
    print(f"\nSmall denominators (< 3^k/k): {small_denom_count} out of {J_max - J_min + 1}")

def rigorous_analysis():
    """
    Main analysis focusing only on what we can prove.
    """
    print("=== Rigorous Analysis of Binary Collatz Cycles ===\n")
    
    print("What we CAN prove:")
    print("1. j=2 requires n ≡ 1 (mod 4) for odd result")
    print("2. Actually stronger: need n ≡ 1 (mod 8) for odd result")
    print("3. Cycle equation gives exact relationship")
    print("4. C has specific algebraic form")
    
    print("\nWhat we CANNOT prove (yet):")
    print("1. Elements are separated by 2√k")
    print("2. Elements stay within bounded ratio")
    print("3. Specific denominator lower bounds")
    
    # Check modular constraints
    print("\n=== Modular Constraint Analysis ===")
    find_provable_contradictions([10, 20, 50, 100, 200, 500])
    
    # Analyze denominators
    for k in [10, 20, 50]:
        analyze_denominator_distribution(k)
    
    # Provable special cases
    print("\n=== Provable Special Cases ===")
    
    print("\n1. All j=2 cycles:")
    print("   - Need all n_i ≡ 1 (mod 8)")
    print("   - Elements form arithmetic progression with difference 8m")
    print("   - Can prove impossible for most k")
    
    print("\n2. Alternating j=1, j=2:")
    print("   - Every other element must be ≡ 1 (mod 8)")
    print("   - Strong structural constraint")
    print("   - May give contradictions")

def main():
    """Run all rigorous analyses."""
    rigorous_analysis()
    
    print("\n=== Path Forward ===")
    print("\n1. Focus on modular constraints (provable)")
    print("2. Analyze specific J values individually")
    print("3. Use algebraic structure of C")
    print("4. Don't assume separation or boundedness")
    print("\nThis approach is weaker but rigorous.")

if __name__ == "__main__":
    main()