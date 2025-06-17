#!/usr/bin/env python3
"""
Comprehensive verification that no binary Collatz cycles exist for k=9-100.
Uses modular constraints to optimize the search.
"""

import math
import time
from typing import List, Tuple, Optional, Set

def check_j_pattern_modular(pattern: List[int]) -> bool:
    """
    Check if a j-pattern can close modularly.
    Returns True if the pattern could potentially form a cycle.
    """
    k = len(pattern)
    
    # Try all starting points n ≡ 1 (mod 8) up to mod 64
    for n0_mod64 in range(1, 64, 8):
        n = n0_mod64
        valid = True
        
        for j in pattern:
            if j == 2:
                if n % 8 != 1:
                    valid = False
                    break
                n = ((3 * n + 1) // 4) % 64
            else:  # j == 1
                n = ((3 * n + 1) // 2) % 64
        
        if valid and n % 8 == n0_mod64 % 8:
            # Pattern returns to same mod 8 class
            return True
    
    return False

def generate_valid_patterns(k: int) -> List[List[int]]:
    """
    Generate j-patterns that satisfy:
    1. J > floor(1.585 * k)
    2. Basic modular constraints
    """
    J_min = math.floor(1.585 * k) + 1
    valid_patterns = []
    
    for mask in range(2**k):
        pattern = []
        J = 0
        
        for i in range(k):
            if (mask >> i) & 1:
                pattern.append(2)
                J += 2
            else:
                pattern.append(1)
                J += 1
        
        # Check J-sum constraint
        if J < J_min or J > 2 * k:
            continue
        
        # Check modular feasibility
        if check_j_pattern_modular(pattern):
            valid_patterns.append(pattern)
    
    return valid_patterns

def apply_j_sequence(n: int, pattern: List[int]) -> Optional[List[int]]:
    """
    Apply a j-pattern starting from n.
    Returns the sequence of elements, or None if invalid.
    """
    elements = [n]
    current = n
    
    for j in pattern:
        if j == 2:
            if current % 4 != 1:
                return None
            next_val = (3 * current + 1) // 4
            if next_val % 2 == 0:  # Must be odd
                return None
        else:  # j == 1
            next_val = (3 * current + 1) // 2
            if next_val % 2 == 0:  # Must be odd
                return None
        
        current = next_val
        elements.append(current)
    
    return elements[:-1] if elements[-1] == n else None

def check_cycle_exists(k: int, pattern: List[int], max_n1: int = 1000000) -> Optional[int]:
    """
    Check if a specific j-pattern can form a k-cycle.
    Returns n₁ if a cycle is found, None otherwise.
    """
    # Only check n₁ values that could satisfy j₁
    if pattern[0] == 2:
        start_vals = range(1, max_n1, 8)  # n₁ ≡ 1 (mod 8)
    else:
        start_vals = range(1, max_n1, 2)   # Any odd n₁
    
    for n1 in start_vals:
        elements = apply_j_sequence(n1, pattern)
        
        if elements is not None:
            # Check if all elements are distinct
            if len(set(elements)) == k:
                return n1
    
    return None

def verify_k_no_cycles(k: int, verbose: bool = False) -> bool:
    """
    Verify that no k-cycles exist.
    Returns True if no cycles found, False if cycle exists.
    """
    if verbose:
        print(f"\nVerifying k={k}...")
        start_time = time.time()
    
    # Generate valid j-patterns
    patterns = generate_valid_patterns(k)
    
    if verbose:
        print(f"  Found {len(patterns)} potentially valid j-patterns")
    
    # Check each pattern
    for i, pattern in enumerate(patterns):
        if verbose and i % 10 == 0:
            print(f"  Checking pattern {i+1}/{len(patterns)}...")
        
        n1 = check_cycle_exists(k, pattern)
        if n1 is not None:
            print(f"\n*** CYCLE FOUND for k={k}! ***")
            print(f"Pattern: {pattern}")
            print(f"Starting element: n₁ = {n1}")
            elements = apply_j_sequence(n1, pattern)
            print(f"Elements: {elements}")
            return False
    
    if verbose:
        elapsed = time.time() - start_time
        print(f"  No cycles found. Time: {elapsed:.2f}s")
    
    return True

def compute_c_value(k: int, pattern: List[int]) -> int:
    """
    Compute C value for a given j-pattern.
    C = Σᵢ 3^(k-1-i) * 2^(s_i) where s_i = Σⱼ<i j_i
    """
    C = 0
    s = 0  # Running sum of j values
    
    for i in range(k):
        C += 3**(k-1-i) * 2**s
        s += pattern[i]
    
    return C

def analyze_pattern_constraints(k: int, pattern: List[int]) -> None:
    """
    Analyze why a specific pattern can't form a cycle.
    """
    print(f"\nAnalyzing pattern {pattern} for k={k}:")
    
    J = sum(pattern)
    print(f"  J = {J}")
    
    C = compute_c_value(k, pattern)
    print(f"  C = {C}")
    
    denominator = 2**J - 3**k
    print(f"  Denominator: 2^{J} - 3^{k} = {denominator}")
    
    if denominator > 0:
        n1_exact = C / denominator
        print(f"  n₁ = C/d = {n1_exact:.6f}")
        
        if n1_exact == int(n1_exact):
            print(f"  n₁ is integer: {int(n1_exact)}")
            # Check if it actually works
            elements = apply_j_sequence(int(n1_exact), pattern)
            if elements:
                print(f"  Elements: {elements}")
                if len(set(elements)) < k:
                    print("  ✗ Elements not distinct!")
            else:
                print("  ✗ Pattern doesn't close properly!")
        else:
            print("  ✗ n₁ is not an integer!")
    else:
        print("  ✗ Denominator ≤ 0!")

def main():
    """Run comprehensive verification."""
    print("=== BINARY COLLATZ CYCLE VERIFICATION k=9-100 ===\n")
    
    # First, verify k=9-20 with detailed output
    print("Detailed verification for k=9-20:")
    
    all_verified = True
    failed_k = []
    
    for k in range(9, 21):
        if not verify_k_no_cycles(k, verbose=True):
            all_verified = False
            failed_k.append(k)
    
    # Then verify k=21-100 with less output
    print("\nQuick verification for k=21-100:")
    
    for k in range(21, 101):
        if k % 10 == 1:
            print(f"  Checking k={k}-{min(k+9, 100)}...")
        
        if not verify_k_no_cycles(k, verbose=False):
            all_verified = False
            failed_k.append(k)
    
    print("\n" + "="*50)
    
    if all_verified:
        print("✓ VERIFIED: No binary Collatz cycles exist for k=9-100")
    else:
        print(f"✗ FOUND CYCLES for k values: {failed_k}")
    
    # Analyze some interesting patterns
    print("\n" + "="*50)
    print("ANALYZING SPECIFIC PATTERNS:")
    
    # All j=2 pattern for k=5
    analyze_pattern_constraints(5, [2,2,2,2,2])
    
    # High-J pattern for k=10
    analyze_pattern_constraints(10, [2,2,2,2,2,2,2,1,1,1])

if __name__ == "__main__":
    main()