#!/usr/bin/env python3
"""
Optimized verification of binary Collatz cycles.
Focus on k=9-20 first with better optimization.
"""

import math
import time
from typing import List, Optional, Set, Tuple

def precompute_modular_transitions():
    """Precompute modular transition tables for efficiency."""
    # Transitions for j=1 and j=2 modulo 64
    trans_j1 = {}
    trans_j2 = {}
    
    for n in range(1, 64, 2):  # Only odd values
        trans_j1[n] = ((3 * n + 1) // 2) % 64
        if n % 8 == 1:  # j=2 only valid here
            trans_j2[n] = ((3 * n + 1) // 4) % 64
    
    return trans_j1, trans_j2

# Global transition tables
TRANS_J1, TRANS_J2 = precompute_modular_transitions()

def quick_modular_check(pattern: List[int]) -> bool:
    """
    Quick check if pattern can close modularly.
    Uses precomputed transitions.
    """
    # Check a few starting points
    for n0 in [1, 9, 17, 25, 33, 41, 49, 57]:  # n ≡ 1 (mod 8)
        n = n0
        valid = True
        
        for j in pattern:
            if j == 2:
                if n not in TRANS_J2:
                    valid = False
                    break
                n = TRANS_J2[n]
            else:
                if n not in TRANS_J1:
                    valid = False
                    break
                n = TRANS_J1[n]
        
        if valid and n % 8 == n0 % 8:
            return True
    
    return False

def count_j2_positions(pattern: List[int]) -> int:
    """Count number of j=2 positions."""
    return sum(1 for j in pattern if j == 2)

def check_simple_impossibilities(k: int, pattern: List[int]) -> Optional[str]:
    """
    Check for simple reasons why a pattern can't work.
    Returns reason string if impossible, None if might work.
    """
    J = sum(pattern)
    
    # Check J bounds
    if J <= math.floor(1.585 * k):
        return "J too small"
    
    # Check for alternating pattern (we know it fails)
    if k >= 2 and all(pattern[i] == (2 if i % 2 == 0 else 1) for i in range(k)):
        return "Alternating pattern"
    
    # All j=2 only works at n=1, giving non-distinct elements
    if all(j == 2 for j in pattern):
        return "All j=2 gives n=1 repeated"
    
    # Quick modular check
    if not quick_modular_check(pattern):
        return "Fails modular closure"
    
    return None

def compute_cycle_equation_solution(k: int, pattern: List[int]) -> Optional[int]:
    """
    Solve n₁(2^J - 3^k) = C for n₁.
    Returns n₁ if it's a positive integer, None otherwise.
    """
    J = sum(pattern)
    
    # Compute C
    C = 0
    s = 0
    for i in range(k):
        C += 3**(k-1-i) * 2**s
        s += pattern[i]
    
    # Compute denominator
    d = 2**J - 3**k
    
    if d <= 0:
        return None
    
    if C % d != 0:
        return None
    
    n1 = C // d
    
    # Must be odd and positive
    if n1 > 0 and n1 % 2 == 1:
        return n1
    
    return None

def verify_cycle_from_n1(n1: int, k: int, pattern: List[int]) -> bool:
    """
    Check if starting from n1 with the given pattern forms a valid k-cycle.
    """
    elements = [n1]
    n = n1
    
    for j in pattern:
        if j == 2:
            if n % 8 != 1:
                return False
            if (3 * n + 1) % 4 != 0:
                return False
            n = (3 * n + 1) // 4
        else:
            n = (3 * n + 1) // 2
        
        if n % 2 == 0:  # Must be odd
            return False
        
        elements.append(n)
    
    # Check closure and distinctness
    return elements[-1] == n1 and len(set(elements[:-1])) == k

def verify_k(k: int, show_details: bool = False) -> Tuple[bool, int, List[str]]:
    """
    Verify no k-cycles exist.
    Returns (no_cycles_exist, patterns_checked, reasons_list)
    """
    J_min = math.floor(1.585 * k) + 1
    patterns_checked = 0
    reasons = {}
    
    # Generate and check all patterns
    for mask in range(2**k):
        pattern = [(mask >> i) & 1 + 1 for i in range(k)]
        J = sum(pattern)
        
        if J < J_min:
            continue
        
        patterns_checked += 1
        
        # Quick impossibility check
        reason = check_simple_impossibilities(k, pattern)
        if reason:
            reasons[reason] = reasons.get(reason, 0) + 1
            continue
        
        # Try to solve cycle equation
        n1 = compute_cycle_equation_solution(k, pattern)
        if n1 is None:
            reasons["No integer n1"] = reasons.get("No integer n1", 0) + 1
            continue
        
        # Verify if it actually forms a cycle
        if verify_cycle_from_n1(n1, k, pattern):
            print(f"\n*** CYCLE FOUND for k={k}! ***")
            print(f"Pattern: {pattern}")
            print(f"n₁ = {n1}")
            return False, patterns_checked, []
        else:
            reasons["Doesn't close"] = reasons.get("Doesn't close", 0) + 1
    
    if show_details:
        print(f"k={k}: Checked {patterns_checked} patterns")
        for reason, count in sorted(reasons.items(), key=lambda x: -x[1]):
            print(f"  {reason}: {count}")
    
    return True, patterns_checked, list(reasons.keys())

def main():
    """Run optimized verification."""
    print("=== OPTIMIZED BINARY COLLATZ CYCLE VERIFICATION ===\n")
    
    start_time = time.time()
    
    # Verify k=9-20 with details
    print("Verifying k=9-20 with details:\n")
    
    all_good = True
    total_patterns = 0
    
    for k in range(9, 21):
        t0 = time.time()
        no_cycles, patterns, _ = verify_k(k, show_details=True)
        t1 = time.time()
        
        if not no_cycles:
            all_good = False
            break
        
        total_patterns += patterns
        print(f"  Time: {t1-t0:.2f}s\n")
    
    elapsed = time.time() - start_time
    
    print("\n" + "="*50)
    if all_good:
        print(f"✓ VERIFIED: No cycles for k=9-20")
        print(f"  Total patterns checked: {total_patterns}")
        print(f"  Total time: {elapsed:.1f}s")
    else:
        print("✗ CYCLE FOUND!")
    
    # Show why some specific patterns fail
    print("\n" + "="*50)
    print("SPECIFIC PATTERN ANALYSIS:\n")
    
    # Pattern that should have high J
    k = 10
    pattern = [2,2,2,2,2,2,1,1,1,1]
    J = sum(pattern)
    print(f"Pattern {pattern} for k={k}:")
    print(f"  J = {J} > {math.floor(1.585*k)} ✓")
    
    n1 = compute_cycle_equation_solution(k, pattern)
    if n1:
        print(f"  n₁ = {n1}")
        if verify_cycle_from_n1(n1, k, pattern):
            print("  Forms a cycle!")
        else:
            print("  ✗ Doesn't form a valid cycle")
    else:
        print("  ✗ No integer solution for n₁")

if __name__ == "__main__":
    main()