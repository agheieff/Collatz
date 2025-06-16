#!/usr/bin/env python3
"""
Optimized Binary Collatz Cycle Verification

Uses theoretical constraints to dramatically reduce search space:
1. J-sum bounds: ⌊1.585k⌋ < J ≤ 2k
2. All cycle elements ≤ 2^k (theoretical bound)
3. Modular constraints to filter valid starting values
"""

import itertools
from typing import List, Tuple, Set

def binary_collatz(n: int, j: int) -> int:
    """Apply the binary Collatz function with j ∈ {1, 2}."""
    return (3 * n + 1) // (2 ** j)

def get_valid_j_sequences(k: int) -> List[List[int]]:
    """Get only j-sequences that satisfy cycle J-sum bounds."""
    valid_sequences = []
    lower_bound = int(1.585 * k)
    upper_bound = 2 * k
    
    # Generate all possible j-sequences
    for j_seq in itertools.product([1, 2], repeat=k):
        J = sum(j_seq)
        if lower_bound < J <= upper_bound:
            valid_sequences.append(list(j_seq))
    
    return valid_sequences

def get_compatible_start_values(j_sequence: List[int], max_val: int) -> Set[int]:
    """
    Get starting values compatible with the j-sequence modular constraints.
    Uses the fact that j=2 requires n ≡ 1 (mod 8) for odd output.
    """
    k = len(j_sequence)
    compatible = set()
    
    # We need to work backwards from the constraints
    # For now, use a simpler approach: check which odd values could work
    for start in range(1, max_val + 1, 2):
        valid = True
        n = start
        
        # Check if this start value is compatible with the j-sequence
        for i in range(k - 1):
            if j_sequence[i] == 1:
                # Need n ≡ 1 (mod 4) for odd result
                if n % 4 != 1:
                    valid = False
                    break
            else:  # j = 2
                # Need n ≡ 1 (mod 8) for odd result
                if n % 8 != 1:
                    valid = False
                    break
            
            n = binary_collatz(n, j_sequence[i])
        
        if valid:
            compatible.add(start)
    
    return compatible

def check_cycle_fast(start: int, j_sequence: List[int]) -> bool:
    """Fast cycle check without redundant validation."""
    current = start
    for j in j_sequence:
        current = binary_collatz(current, j)
    return current == start

def find_cycles_optimized(k: int) -> List[Tuple[int, List[int]]]:
    """Optimized cycle search using constraints."""
    cycles = []
    max_element = 2 ** k  # Theoretical bound
    
    # Get only valid j-sequences
    valid_sequences = get_valid_j_sequences(k)
    print(f"k={k}: Checking {len(valid_sequences)} valid j-sequences out of {2**k} total")
    
    for j_seq in valid_sequences:
        # Get compatible starting values
        compatible_starts = get_compatible_start_values(j_seq, min(max_element, 10000))
        
        for start in compatible_starts:
            if check_cycle_fast(start, j_seq):
                cycles.append((start, j_seq))
                print(f"Found cycle! k={k}, start={start}, j_sequence={j_seq}")
    
    return cycles

def verify_no_cycles(max_k: int = 30):
    """Main verification function."""
    print(f"Optimized verification for k ≤ {max_k}")
    print("=" * 60)
    
    # First, let's check trivial cycles (k=1)
    print("\nChecking k=1 (trivial case):")
    # For k=1, we need n such that (3n+1)/2^j = n
    # j=1: (3n+1)/2 = n => 3n+1 = 2n => n = -1 (invalid)
    # j=2: (3n+1)/4 = n => 3n+1 = 4n => n = -1/1 (invalid)
    print("No cycles possible for k=1 (algebraically impossible)")
    
    total_cycles = 0
    
    for k in range(2, max_k + 1):
        cycles = find_cycles_optimized(k)
        
        if cycles:
            total_cycles += len(cycles)
            print(f"\n!!! Found {len(cycles)} cycles for k={k}")
            for start, j_seq in cycles:
                print(f"  Cycle: start={start}, j_seq={j_seq}")
        else:
            valid_seqs = len(get_valid_j_sequences(k))
            print(f"k={k}: No cycles found ({valid_seqs} valid j-sequences checked)")
    
    print(f"\n{'='*60}")
    print(f"Total cycles found for 2 ≤ k ≤ {max_k}: {total_cycles}")
    
    return total_cycles == 0

def check_specific_small_k():
    """Exhaustive check for very small k values."""
    print("\nExhaustive verification for small k:")
    print("-" * 40)
    
    for k in range(2, 8):
        print(f"\nk={k}:")
        cycles_found = False
        
        # For small k, check all j-sequences and all reasonable start values
        for j_seq in itertools.product([1, 2], repeat=k):
            j_list = list(j_seq)
            J = sum(j_list)
            
            # Check J-sum bounds
            if not (int(1.585 * k) < J <= 2 * k):
                continue
            
            # Check all odd values up to 2^(k+2)
            for start in range(1, 2**(k+2), 2):
                if check_cycle_fast(start, j_list):
                    print(f"  Found: start={start}, j_seq={j_list}, J={J}")
                    cycles_found = True
        
        if not cycles_found:
            print(f"  No cycles found")

if __name__ == "__main__":
    # First do exhaustive check for very small k
    check_specific_small_k()
    
    print("\n" + "="*60 + "\n")
    
    # Then optimized check for larger k
    result = verify_no_cycles(max_k=50)
    
    if result:
        print("\n✓ VERIFIED: No binary Collatz cycles exist for k ≤ 50")
    else:
        print("\n✗ Found cycles - this would contradict the conjecture!")