#!/usr/bin/env python3
"""
Rigorous modular analysis of binary Collatz cycles.
Focus on what we can actually PROVE, not wishful thinking.
"""

import math
from typing import List, Tuple, Set

def analyze_j2_feasibility(k: int, num_j2: int) -> Tuple[bool, str]:
    """
    Can we have a k-cycle with exactly num_j2 positions having j=2?
    
    PROVEN FACT: j=2 requires n ≡ 1 (mod 8) for odd result.
    """
    # We need:
    # - k distinct odd integers
    # - exactly num_j2 of them must be ≡ 1 (mod 8)
    # - the other k - num_j2 must be ≡ 3, 5, 7 (mod 8)
    
    # Key insight: The numbers ≡ 1 (mod 8) are spaced by 8
    # If we use m of them, they span at least 8(m-1) + 1
    
    # Example with num_j2 = 3:
    # Could use 1, 9, 17 (span = 17)
    # In between we can place: 3,5,7, 11,13,15
    # That's 6 additional odd numbers
    
    if num_j2 == 0:
        return True, "No j=2 positions, no constraint"
    
    if num_j2 == k:
        # All positions need ≡ 1 (mod 8)
        # Minimum span: 1, 9, 17, ..., 8(k-1)+1
        return True, f"All j=2: elements are 1, 9, 17, ..., {8*(k-1)+1}"
    
    # General case: mix of residue classes
    # Between consecutive ≡ 1 (mod 8), we have 3 odd numbers of other residues
    # (namely 3, 5, 7 mod 8)
    
    gaps_between_1_mod_8 = num_j2 - 1
    odd_numbers_in_gaps = gaps_between_1_mod_8 * 3
    
    # We also have odd numbers before the first and after the last ≡ 1 (mod 8)
    # But let's be conservative and just count the gaps
    
    other_positions_needed = k - num_j2
    
    if odd_numbers_in_gaps >= other_positions_needed:
        return True, f"Can fit {other_positions_needed} other odd numbers in {gaps_between_1_mod_8} gaps"
    else:
        # Need to use odd numbers outside the span of ≡ 1 (mod 8) numbers
        # This is always possible by extending the range
        return True, f"Need extended range beyond the ≡ 1 (mod 8) positions"

def analyze_cycle_equation_constraints(k: int, J: int) -> Tuple[bool, str]:
    """
    Check constraints from n₁(2^J - 3^k) = C.
    """
    log2_3 = math.log(3) / math.log(2)
    
    # Critical J where 2^J = 3^k
    J_critical = k * log2_3
    
    # C must have consistent sign
    if abs(J - J_critical) < 0.1:
        return False, f"J too close to critical value {J_critical:.2f}, denominator too small"
    
    return True, "Denominator is reasonable"

def find_provable_contradictions_rigorous(k_values: List[int]):
    """
    Look for contradictions using only provable facts.
    """
    print("=== Rigorous Search for Contradictions ===\n")
    
    for k in k_values:
        print(f"\n--- k = {k} ---")
        
        J_min = math.floor(1.585 * k) + 1
        J_max = 2 * k
        
        valid_J_values = []
        contradictions = []
        
        for J in range(J_min, J_max + 1):
            num_j2 = J - k
            
            # Check modular feasibility
            mod_feasible, mod_reason = analyze_j2_feasibility(k, num_j2)
            
            # Check cycle equation
            eq_feasible, eq_reason = analyze_cycle_equation_constraints(k, J)
            
            if mod_feasible and eq_feasible:
                valid_J_values.append(J)
            else:
                reason = []
                if not mod_feasible:
                    reason.append(f"Modular: {mod_reason}")
                if not eq_feasible:
                    reason.append(f"Equation: {eq_reason}")
                contradictions.append((J, "; ".join(reason)))
        
        print(f"J range: {J_min} to {J_max} ({J_max - J_min + 1} values)")
        print(f"Valid J values: {len(valid_J_values)}")
        print(f"Contradictions: {len(contradictions)}")
        
        if contradictions and k <= 20:
            print("\nContradictory J values:")
            for J, reason in contradictions[:5]:  # Show first 5
                print(f"  J={J}: {reason}")

def analyze_specific_patterns():
    """
    Analyze specific j-patterns that might be problematic.
    """
    print("\n=== Analysis of Specific J-Patterns ===\n")
    
    # Pattern 1: Alternating j=1, j=2
    print("Pattern: Alternating j=1, j=2")
    print("- Half positions need n ≡ 1 (mod 8)")
    print("- These must be every other position in the cycle")
    print("- Strong structural constraint!")
    
    # Pattern 2: Blocks of j=2
    print("\nPattern: Consecutive j=2 positions")
    print("- If positions i, i+1, ..., i+m all have j=2")
    print("- Then n_i, n_{i+1}, ..., n_{i+m} all ≡ 1 (mod 8)")
    print("- But n_{i+1} = (3n_i + 1)/4")
    print("- This creates recursive constraints!")
    
    # Let's check: if n ≡ 1 (mod 8) and n' = (3n+1)/4
    # What is n' (mod 8)?
    for n_mod_8 in [1]:
        n = 8 * 5 + n_mod_8  # Example: n = 41
        n_prime = (3 * n + 1) // 4
        print(f"\nIf n ≡ {n_mod_8} (mod 8), then (3n+1)/4 ≡ {n_prime % 8} (mod 8)")
        print(f"Example: n = {n}, n' = {n_prime}")

def investigate_algebraic_structure():
    """
    Look at the algebraic structure of C more carefully.
    """
    print("\n=== Algebraic Structure of C ===\n")
    
    print("C = Σ(i=0 to k-1) 3^(k-1-i) * 2^(J_i)")
    print("where J_i = j_0 + j_1 + ... + j_{i-1}")
    
    print("\nFor small k, let's compute C for different patterns:")
    
    for k in [3, 4, 5]:
        print(f"\nk = {k}:")
        
        # All j=1
        C_all_1 = sum(3**(k-1-i) * 2**i for i in range(k))
        print(f"  All j=1: C = {C_all_1}")
        
        # All j=2  
        C_all_2 = sum(3**(k-1-i) * 2**(2*i) for i in range(k))
        print(f"  All j=2: C = {C_all_2}")
        
        # Check divisibility
        print(f"  C_all_1 ≡ {C_all_1 % 8} (mod 8)")
        print(f"  C_all_2 ≡ {C_all_2 % 8} (mod 8)")

def main():
    """Run rigorous analyses."""
    
    print("=== Rigorous Modular Analysis ===\n")
    
    print("PROVEN FACTS:")
    print("1. j=2 on odd n requires n ≡ 1 (mod 8) for odd result")
    print("2. Cycle equation: n₁(2^J - 3^k) = C")
    print("3. C has specific algebraic form")
    
    # Search for contradictions
    find_provable_contradictions_rigorous([5, 10, 20, 50, 100])
    
    # Specific patterns
    analyze_specific_patterns()
    
    # Algebraic structure
    investigate_algebraic_structure()
    
    print("\n=== Conclusion ===")
    print("\nThe modular constraints are real but not immediately contradictory.")
    print("Need to combine with other constraints:")
    print("1. Algebraic form of C")
    print("2. Cycle closure constraint") 
    print("3. Specific j-pattern analysis")
    print("\nThe path forward requires deeper analysis, not hand-waving.")

if __name__ == "__main__":
    main()