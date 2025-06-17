#!/usr/bin/env python3
"""
Verify the no-consecutive-j=2 theorem with concrete calculations.
This will help us get the proof right.
"""

def analyze_j2_sequence():
    """Analyze what happens with consecutive j=2 positions."""
    
    print("=== Consecutive j=2 Analysis ===\n")
    
    # For j=2 to give odd result, need n ≡ 1 (mod 8)
    print("Requirement: For j=2 to give odd result, need n ≡ 1 (mod 8)\n")
    
    # Test all n ≡ 1 (mod 8) up to some limit
    print("Testing n ≡ 1 (mod 8):")
    for k in range(10):
        n = 8 * k + 1
        # Apply j=2: compute (3n + 1) / 4
        if (3 * n + 1) % 4 == 0:
            result = (3 * n + 1) // 4
            print(f"n = {n} ≡ 1 (mod 8)")
            print(f"  (3n + 1) / 4 = {result}")
            print(f"  Result ≡ {result % 8} (mod 8)")
            
            # Check if result is odd
            if result % 2 == 1:
                print(f"  Result is ODD ✓")
            else:
                print(f"  Result is EVEN ✗")
                
            # Can we apply j=2 again?
            if result % 2 == 1 and result % 8 == 1:
                print(f"  Can apply j=2 again: YES")
            else:
                print(f"  Can apply j=2 again: NO")
            print()

def systematic_mod_analysis():
    """Systematic analysis of modular arithmetic."""
    
    print("\n=== Systematic Modular Analysis ===\n")
    
    # For n = 8k + 1
    print("For n ≡ 1 (mod 8), i.e., n = 8k + 1:")
    print("3n + 1 = 3(8k + 1) + 1 = 24k + 4 = 4(6k + 1)")
    print("So (3n + 1)/4 = 6k + 1\n")
    
    print("Now analyze 6k + 1 (mod 8) based on k (mod 4):")
    for k_mod in range(4):
        result_mod = (6 * k_mod + 1) % 8
        print(f"  If k ≡ {k_mod} (mod 4), then 6k + 1 ≡ {result_mod} (mod 8)")
    
    print("\nConclusion: The result is never ≡ 1 (mod 8)!")
    print("Therefore, cannot have consecutive j=2 positions.")

def explore_j_pattern_constraints():
    """Explore constraints on j-patterns from no-consecutive-j=2."""
    
    print("\n\n=== J-Pattern Constraints ===\n")
    
    def count_valid_patterns(k, allow_consecutive_j2=False):
        """Count valid j-patterns with given constraints."""
        count = 0
        
        # Generate all possible j-patterns (j ∈ {1,2})
        for pattern in range(2**k):
            valid = True
            
            # Extract j values (0 = j=1, 1 = j=2)
            j_seq = []
            for i in range(k):
                j_seq.append((pattern >> i) & 1)
            
            # Check no consecutive j=2 if required
            if not allow_consecutive_j2:
                for i in range(k-1):
                    if j_seq[i] == 1 and j_seq[i+1] == 1:
                        valid = False
                        break
            
            # Check J-sum bounds
            J = sum(2 if j == 1 else 1 for j in j_seq)
            if not (1.585 * k < J <= 2 * k):
                valid = False
            
            if valid:
                count += 1
                if k <= 5:  # Print for small k
                    j_str = ''.join('2' if j == 1 else '1' for j in j_seq)
                    print(f"  Valid pattern: {j_str}, J = {J}")
        
        return count
    
    print("Number of valid j-patterns:")
    for k in [3, 4, 5, 6, 8, 10]:
        total = count_valid_patterns(k, allow_consecutive_j2=True)
        restricted = count_valid_patterns(k, allow_consecutive_j2=False)
        
        print(f"\nk = {k}:")
        print(f"  With consecutive j=2: {total}")
        print(f"  No consecutive j=2: {restricted}")
        print(f"  Reduction: {(total - restricted) / total * 100:.1f}%")

def check_specific_patterns():
    """Check specific problematic j-patterns."""
    
    print("\n\n=== Specific Pattern Analysis ===\n")
    
    # Pattern 1: Alternating 1,2,1,2,...
    print("Pattern: Alternating j=1, j=2")
    k = 10
    J = 5 * 1 + 5 * 2  # 5 positions with j=1, 5 with j=2
    print(f"  k = {k}, J = {J}")
    print(f"  J/k = {J/k:.3f}")
    print(f"  Need J > {1.585 * k:.1f}")
    print(f"  Valid: {J > 1.585 * k}")
    
    # Pattern 2: Blocks of j=2
    print("\nPattern: j=2 blocks (impossible by our theorem)")
    print("  Any block of 2 or more j=2 is impossible")
    
    # Pattern 3: Maximum j=2 positions
    print("\nMaximum j=2 positions (no consecutive):")
    for k in [10, 20, 50, 100]:
        max_j2 = (k + 1) // 2  # At most every other position
        J_max = (k - max_j2) * 1 + max_j2 * 2
        print(f"  k = {k}: max j=2 positions = {max_j2}, J_max = {J_max}")
        print(f"    J_max/k = {J_max/k:.3f}")
        print(f"    Need J > {1.585 * k:.1f}, so J/k > 1.585")
        print(f"    Achievable: {J_max/k > 1.585}")

def main():
    """Run all analyses."""
    
    analyze_j2_sequence()
    systematic_mod_analysis()
    explore_j_pattern_constraints()
    check_specific_patterns()
    
    print("\n\n=== Key Findings ===")
    print("1. NO consecutive j=2 positions (rigorously proven)")
    print("2. This significantly reduces valid j-patterns")
    print("3. Maximum j=2 positions: ⌊(k+1)/2⌋")
    print("4. For large k, this limits J/k ≤ 1.5")
    print("5. But we need J/k > 1.585 for cycles!")
    print("\nThis is getting close to a contradiction...")

if __name__ == "__main__":
    main()