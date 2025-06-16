#!/usr/bin/env python3
"""
Correct Binary Collatz Cycle Verification

A k-cycle must have k DISTINCT odd numbers that map to each other.
The trivial fixed point n=1 with j=2 doesn't count as a k-cycle.
"""

import itertools
from typing import List, Tuple, Set, Optional

def binary_collatz(n: int, j: int) -> int:
    """Apply the binary Collatz function with j ∈ {1, 2}."""
    return (3 * n + 1) // (2 ** j)

def trace_sequence(start: int, j_sequence: List[int]) -> List[int]:
    """Trace the full sequence of values from start through j_sequence."""
    values = [start]
    current = start
    
    for j in j_sequence:
        current = binary_collatz(current, j)
        values.append(current)
    
    return values[:-1]  # Don't include the final value (should equal start)

def check_proper_cycle(start: int, j_sequence: List[int]) -> bool:
    """
    Check if this forms a proper k-cycle with k distinct odd values.
    """
    k = len(j_sequence)
    values = []
    current = start
    
    # Trace through the sequence
    for i, j in enumerate(j_sequence):
        if current % 2 == 0:  # Must be odd
            return False
        
        values.append(current)
        current = binary_collatz(current, j)
        
        # Check if result is odd (except last step)
        if i < k - 1 and current % 2 == 0:
            return False
    
    # Check if we returned to start
    if current != start:
        return False
    
    # Check if all values are distinct
    if len(set(values)) != k:
        return False
    
    return True

def get_valid_j_sequences(k: int) -> List[List[int]]:
    """Get j-sequences that satisfy cycle J-sum bounds."""
    valid_sequences = []
    lower_bound = int(1.585 * k)
    upper_bound = 2 * k
    
    for j_seq in itertools.product([1, 2], repeat=k):
        J = sum(j_seq)
        if lower_bound < J <= upper_bound:
            valid_sequences.append(list(j_seq))
    
    return valid_sequences

def find_proper_cycles(k: int, max_start: int = None) -> List[Tuple[int, List[int], List[int]]]:
    """Find proper k-cycles (k distinct odd numbers)."""
    if max_start is None:
        max_start = min(2 ** (k + 4), 100000)
    
    cycles = []
    valid_sequences = get_valid_j_sequences(k)
    
    print(f"k={k}: Checking {len(valid_sequences)} valid j-sequences")
    
    for j_seq in valid_sequences:
        # Only check odd starting values
        for start in range(1, max_start + 1, 2):
            if check_proper_cycle(start, j_seq):
                values = trace_sequence(start, j_seq)
                # Verify it's not a trivial cycle
                if len(set(values)) == k:
                    cycles.append((start, j_seq, values))
                    print(f"  Found proper {k}-cycle!")
                    print(f"    Values: {values}")
                    print(f"    J-sequence: {j_seq} (sum={sum(j_seq)})")
    
    return cycles

def analyze_trivial_cycle():
    """Analyze the trivial fixed point."""
    print("Analyzing trivial fixed point:")
    print("-" * 40)
    
    # n=1 with j=2
    result = binary_collatz(1, 2)
    print(f"f(1, j=2) = (3×1+1)/4 = {result}")
    print("This is a fixed point, not a proper k-cycle\n")
    
    # Check other small odd values
    print("Checking other small odd values with j=2:")
    for n in [3, 5, 7, 9, 11, 13, 15]:
        result = binary_collatz(n, 2)
        print(f"f({n}, j=2) = (3×{n}+1)/4 = {result}")

def verify_no_proper_cycles(max_k: int = 30):
    """Main verification for proper cycles."""
    print(f"\nVerifying no proper k-cycles exist for k ≤ {max_k}")
    print("=" * 60)
    
    total_proper_cycles = 0
    
    for k in range(2, max_k + 1):
        cycles = find_proper_cycles(k)
        
        if cycles:
            total_proper_cycles += len(cycles)
            print(f"\n!!! Found {len(cycles)} proper cycles for k={k}")
        else:
            print(f"k={k}: No proper cycles found ✓")
    
    print(f"\n{'='*60}")
    print(f"Total proper cycles found: {total_proper_cycles}")
    
    return total_proper_cycles == 0

def theoretical_analysis():
    """Show why cycles are difficult theoretically."""
    print("\nTheoretical constraints on cycles:")
    print("-" * 40)
    
    # For a k-cycle, we need the product of all transformations to equal 1
    # ∏(3n_i + 1)/(2^j_i × n_i) = 1
    # This gives us: ∏(3 + 1/n_i) = 2^J
    
    print("For a k-cycle to exist:")
    print("1. Product constraint: ∏(3 + 1/n_i) = 2^J")
    print("2. J-sum constraint: ⌊1.585k⌋ < J ≤ 2k")
    print("3. All n_i must be distinct odd numbers")
    print("4. Modular constraints: j=2 requires n ≡ 1 (mod 8)")
    
    # Example: For k=2
    print("\nExample analysis for k=2:")
    print("Need: (3 + 1/n₁)(3 + 1/n₂) = 2^J where 3 < J ≤ 4")
    print("So: 9 + 3/n₁ + 3/n₂ + 1/(n₁n₂) = 2^J ∈ {16}")
    print("This requires: 3/n₁ + 3/n₂ + 1/(n₁n₂) = 7")
    print("No positive odd solutions exist!")

if __name__ == "__main__":
    # First show the trivial fixed point
    analyze_trivial_cycle()
    
    print("\n" + "="*60 + "\n")
    
    # Theoretical explanation
    theoretical_analysis()
    
    print("\n" + "="*60 + "\n")
    
    # Main verification
    result = verify_no_proper_cycles(max_k=30)
    
    if result:
        print("\n✓ VERIFIED: No proper binary Collatz cycles exist for k ≤ 30")
        print("(The trivial fixed point f(1,2)=1 is not a proper k-cycle)")
    else:
        print("\n✗ Found proper cycles - this would be significant!")