#!/usr/bin/env python3
"""
Investigate the surprising modular contradiction discovered above.
It seems ALL J values lead to contradictions for the tested k values!
"""

import math

def detailed_modular_analysis(k: int):
    """
    Detailed analysis of why modular constraints give contradictions.
    """
    print(f"\n=== Detailed Analysis for k = {k} ===")
    
    J_min = math.floor(1.585 * k) + 1
    J_max = 2 * k
    
    print(f"J range: {J_min} to {J_max}")
    print(f"Total J values: {J_max - J_min + 1}")
    
    # Key insight: For j=2 to give odd result, need n ≡ 1 (mod 8)
    # (because (3n+1)/4 must be odd)
    
    valid_J_count = 0
    
    for J in range(J_min, J_max + 1):
        num_j2 = J - k
        num_j1 = k - num_j2
        
        # How many positions need n ≡ 1 (mod 8)?
        positions_needing_1_mod_8 = num_j2
        
        # In k distinct odd integers, how many can be ≡ 1 (mod 8)?
        # The odd integers ≡ 1 (mod 8) are: 1, 9, 17, 25, ...
        # These are spaced 8 apart
        
        # If we have k distinct odd integers in a range, 
        # the minimum range is 2(k-1) + 1 = 2k - 1
        # In this range, we have at most ceil((2k-1)/8) numbers ≡ 1 (mod 8)
        
        max_available_1_mod_8 = math.ceil((2*k - 1) / 8)
        
        print(f"\nJ = {J}:")
        print(f"  Need {positions_needing_1_mod_8} positions with n ≡ 1 (mod 8)")
        print(f"  Maximum available: {max_available_1_mod_8}")
        
        if positions_needing_1_mod_8 <= max_available_1_mod_8:
            valid_J_count += 1
            print(f"  → POSSIBLE")
        else:
            print(f"  → CONTRADICTION!")
    
    print(f"\nSummary: {valid_J_count} valid J values out of {J_max - J_min + 1}")
    
    # But wait! This is assuming optimal packing. 
    # The cycle constraint makes it even harder...

def why_was_analysis_wrong():
    """
    The previous analysis was too simplistic. Let's be more careful.
    """
    print("\n=== Correcting the Analysis ===")
    
    print("\nThe error: I assumed minimum range 2k for k odd integers.")
    print("But we need k DISTINCT odd integers, not just any odd integers.")
    
    print("\nCorrected analysis:")
    print("- k distinct odd integers: could be 1, 3, 5, ..., 2k-1")
    print("- Range: 2k-1")
    print("- Numbers ≡ 1 (mod 8) in this range: {1, 9, 17, ..., up to 2k-1}")
    print("- Count: approximately k/4")
    
    print("\nSo we can have at most k/4 positions with j=2")
    print("This means J ≤ k + k/4 = 5k/4")
    
    print("\nBut J must be > 1.585k, so we need:")
    print("1.585k < J ≤ 1.25k")
    print("This is impossible for k > 0!")

def investigate_real_constraint():
    """
    Look at the real constraint more carefully.
    """
    print("\n=== The Real Modular Constraint ===")
    
    print("\nWait, I need to be even more careful...")
    print("\nFor j=2 on odd n:")
    print("- n must satisfy (3n+1) ≡ 0 (mod 4)")
    print("- This means 3n ≡ 3 (mod 4)")
    print("- So n ≡ 1 (mod 4)")
    
    print("\nBut for the result to be odd:")
    print("- (3n+1)/4 must be odd")
    print("- So 3n+1 ≡ 4 (mod 8)")
    print("- So 3n ≡ 3 (mod 8)")
    print("- So n ≡ 1 (mod 8)")
    
    print("\nNow, among k odd integers, how many can be ≡ 1 (mod 8)?")
    
    for k in [10, 20, 50, 100]:
        print(f"\nk = {k}:")
        # Best case: pack them as tightly as possible
        # 1, 9, 17, 25, ... (separated by 8)
        # Can fit at most floor(range/8) + 1
        
        # But what's the minimum range for k distinct odd integers?
        # Not 2k! Could be much larger if we need many ≡ 1 (mod 8)
        
        # If we need m positions ≡ 1 (mod 8), minimum range is 8(m-1) + 1
        # Plus we need k-m other odd positions
        
        J_min = math.floor(1.585 * k) + 1
        J_max = 2 * k
        
        print(f"  J range: {J_min} to {J_max}")
        
        # For each J, check if it's possible
        possible_J = []
        for J in range(J_min, J_max + 1):
            num_j2 = J - k
            # Need num_j2 positions ≡ 1 (mod 8)
            # Need k - num_j2 other odd positions
            
            # Minimum range: place 1 (mod 8) positions optimally
            if num_j2 > 0:
                min_range_for_1_mod_8 = 8 * (num_j2 - 1) + 1
            else:
                min_range_for_1_mod_8 = 0
            
            # But we also need k-num_j2 other odd integers
            # In the gaps between 1 (mod 8) positions, we can place:
            # Between consecutive 1 (mod 8): 3, 5, 7 (3 odd numbers)
            
            if num_j2 >= 2:
                gaps = num_j2 - 1
                odd_in_gaps = gaps * 3
                
                # Before first and after last 1 (mod 8)
                # Can place some, but limited
                
                if odd_in_gaps >= k - num_j2:
                    possible_J.append(J)
            elif num_j2 == 1:
                # Just one position needs ≡ 1 (mod 8)
                # Others can be anywhere
                possible_J.append(J)
            elif num_j2 == 0:
                # All j=1, no constraint
                possible_J.append(J)
        
        print(f"  Possible J values: {len(possible_J)} out of {J_max - J_min + 1}")
        if len(possible_J) < 10:
            print(f"  Specifically: {possible_J}")

def main():
    """Investigate the modular constraints more carefully."""
    
    print("=== Modular Constraints in Binary Collatz Cycles ===")
    
    # First, the detailed analysis
    detailed_modular_analysis(10)
    detailed_modular_analysis(20)
    
    # Why was the original claim too strong?
    why_was_analysis_wrong()
    
    # The real constraint
    investigate_real_constraint()
    
    print("\n=== Conclusion ===")
    print("\nThe modular constraint is strong but not as strong as first claimed.")
    print("Need to be more careful about counting arguments.")
    print("\nHowever, combined with other constraints, this could still give contradictions.")

if __name__ == "__main__":
    main()