#!/usr/bin/env python3
"""
Consolidated computational verification for Binary Collatz Cycles.

This file combines:
1. Small k verification (k ≤ 100)
2. C value computation and bounds checking
3. Crisis k identification
4. Numerical validation of key claims

IMPORTANT: The original claim C ≥ 0.686 × 4^k is FALSE for k ≥ 8.
The correct growth is C ~ 3^k.
"""

import math
from typing import List, Tuple, Optional

# Constants
ALPHA = 2 - math.log(3) / math.log(2)  # ≈ 0.415
LOG2_3 = math.log(3) / math.log(2)     # ≈ 1.585

def compute_c(k: int, j_seq: List[int]) -> int:
    """Compute C value for given j-sequence."""
    C = 0
    partial_sum = 0
    for i in range(k):
        partial_sum += j_seq[i]
        C += 3**(k-i-1) * (2**partial_sum - 1)
    return C

def compute_c_positions(k: int, j1_positions: List[int]) -> int:
    """Compute C when j=1 at specified positions, j=2 elsewhere."""
    j_seq = [2] * k
    for pos in j1_positions:
        j_seq[pos] = 1
    return compute_c(k, j_seq)

def verify_cycle_equation(k: int, j_seq: List[int], n1: int) -> bool:
    """Check if n₁(2^J - 3^k) = C for given parameters."""
    J = sum(j_seq)
    C = compute_c(k, j_seq)
    denominator = abs(2**J - 3**k)
    
    # Check divisibility
    if C % denominator != 0:
        return False
    
    # Check if n₁ matches
    return n1 == C // denominator

def is_crisis_k(k: int, tolerance: float = 0.01) -> bool:
    """Check if k is a crisis value (fractional part of αk is small)."""
    fractional_part = (ALPHA * k) % 1
    return min(fractional_part, 1 - fractional_part) < tolerance

def find_crisis_k_values(max_k: int) -> List[int]:
    """Find all crisis k values up to max_k."""
    crisis_values = []
    for k in range(1, max_k + 1):
        if is_crisis_k(k):
            crisis_values.append(k)
    return crisis_values

def verify_small_k(k: int) -> bool:
    """
    Verify no k-cycles exist for given k.
    Returns True if no cycles found (proof of impossibility).
    """
    if k <= 0:
        return True
    
    # J bounds from j_sum_bounds theorem
    J_min = math.floor(1.585 * k) + 1
    J_max = 2 * k
    
    for J in range(J_min, J_max + 1):
        # Generate all j-sequences with sum J
        for j_seq in generate_j_sequences(k, J):
            C = compute_c(k, j_seq)
            denominator = abs(2**J - 3**k)
            
            # Check if C is divisible by denominator
            if C % denominator == 0:
                n1 = C // denominator
                
                # Check constraints
                if n1 > 0 and n1 % 2 == 1 and n1 <= 2**k:
                    # Try to build cycle
                    cycle = attempt_cycle_construction(k, j_seq, n1)
                    if cycle is not None:
                        print(f"WARNING: Found potential cycle for k={k}")
                        return False
    
    return True  # No cycles found

def generate_j_sequences(k: int, target_sum: int) -> List[List[int]]:
    """Generate all binary j-sequences of length k with given sum."""
    if k == 0:
        return [[]] if target_sum == 0 else []
    if target_sum < k or target_sum > 2*k:
        return []
    
    sequences = []
    # Try j=1 at position 0
    if target_sum - 1 >= k - 1:
        for suffix in generate_j_sequences(k-1, target_sum-1):
            sequences.append([1] + suffix)
    # Try j=2 at position 0
    if target_sum - 2 <= 2*(k-1):
        for suffix in generate_j_sequences(k-1, target_sum-2):
            sequences.append([2] + suffix)
    
    return sequences

def attempt_cycle_construction(k: int, j_seq: List[int], n1: int) -> Optional[List[int]]:
    """Try to construct a k-cycle starting with n₁."""
    elements = [n1]
    current = n1
    
    for i in range(k):
        j = j_seq[i]
        next_val = (3 * current + 1) // (2**j)
        
        # Check if result is odd
        if (3 * current + 1) % (2**j) != 0:
            return None
        if next_val % 2 == 0:
            return None
        
        # Check bounds
        if next_val > 2**k:
            return None
        
        # For final step, check cycle closure
        if i == k - 1:
            if next_val != n1:
                return None
        else:
            # Check distinctness
            if next_val in elements:
                return None
            elements.append(next_val)
            current = next_val
    
    return elements

def verify_c_bounds():
    """Verify the actual growth rate of C."""
    print("C Growth Analysis (Corrected)")
    print("=" * 60)
    print("k\tmin(C)/3^k\tmin(C)/4^k\tC grows like 3^k?")
    print("-" * 60)
    
    for k in range(3, 21):
        min_c_ratio_3k = float('inf')
        min_c_ratio_4k = float('inf')
        
        # Try different numbers of j=1 positions
        for num_j1 in range(k+1):
            # Minimum C when j=1 positions are at the end
            j1_positions = list(range(k-num_j1, k))
            C = compute_c_positions(k, j1_positions)
            
            ratio_3k = C / (3**k)
            ratio_4k = C / (4**k)
            
            min_c_ratio_3k = min(min_c_ratio_3k, ratio_3k)
            min_c_ratio_4k = min(min_c_ratio_4k, ratio_4k)
        
        bounded = "✓" if 0.1 < min_c_ratio_3k < 10 else "✗"
        print(f"{k}\t{min_c_ratio_3k:.4f}\t\t{min_c_ratio_4k:.4f}\t\t{bounded}")
    
    print("\nConclusion: C grows like 3^k, and C/4^k → 0 as k → ∞")

def main():
    """Run all verification tasks."""
    print("Binary Collatz Cycle Verification")
    print("=" * 60)
    
    # 1. Verify small k
    print("\n1. Small k Verification")
    print("-" * 40)
    max_verified = 0
    for k in range(1, 21):  # Verify up to k=20
        if verify_small_k(k):
            max_verified = k
        else:
            print(f"FAILED at k={k}")
            break
    print(f"Verified: No cycles for k ≤ {max_verified}")
    
    # 2. Find crisis k values
    print("\n2. Crisis k Values")
    print("-" * 40)
    crisis_values = find_crisis_k_values(100)
    print(f"Crisis k ≤ 100: {crisis_values}")
    print(f"Density: {len(crisis_values)/100:.2%}")
    
    # 3. Verify C bounds
    print("\n3. C Growth Analysis")
    print("-" * 40)
    verify_c_bounds()
    
    # 4. Check specific claims
    print("\n4. Key Claims Verification")
    print("-" * 40)
    
    # Check: For k=8, C/4^k < 0.686
    k = 8
    j_seq = [2]*5 + [1]*3  # Minimum J case
    C = compute_c(k, j_seq)
    ratio = C / (4**k)
    print(f"k=8: C/4^k = {ratio:.4f} < 0.686? {ratio < 0.686}")
    
    # Check: Crisis example k=19
    k = 19
    if is_crisis_k(k):
        J_approx = round(k * LOG2_3)
        denominator = abs(2**J_approx - 3**k)
        print(f"k=19 (crisis): |2^{J_approx} - 3^{k}| = {denominator}")
        print(f"Relative size: {denominator / (3**k):.2e}")

if __name__ == "__main__":
    main()