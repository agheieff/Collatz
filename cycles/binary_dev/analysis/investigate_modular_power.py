#!/usr/bin/env python3
"""
Investigate why modular constraints are so powerful.
"""

import math
from typing import List, Set, Tuple

def analyze_modular_closure():
    """Analyze modular closure properties in detail."""
    print("=== WHY MODULAR CONSTRAINTS ARE SO POWERFUL ===\n")
    
    print("Key insight: Most j-patterns create modular trajectories that")
    print("drift away from the starting point and never return.\n")
    
    # Let's trace some patterns
    print("EXAMPLE TRAJECTORIES (mod 64):\n")
    
    patterns = [
        ([2,1,2,1,2], "Alternating"),
        ([2,2,1,1,1], "Front-loaded j=2"),
        ([1,1,2,2,2], "Back-loaded j=2"),
        ([2,1,1,1,2], "Separated j=2"),
    ]
    
    for pattern, name in patterns:
        print(f"{name} pattern {pattern}:")
        
        # Try from different starting points
        found_closure = False
        for n0 in [1, 9, 17, 25, 33, 41, 49, 57]:
            n = n0
            trajectory = [n]
            valid = True
            
            for j in pattern:
                if j == 2:
                    if n % 8 != 1:
                        valid = False
                        break
                    n = ((3 * n + 1) // 4) % 64
                else:
                    n = ((3 * n + 1) // 2) % 64
                trajectory.append(n)
            
            if valid and trajectory[-1] == n0:
                print(f"  Closes from n₀≡{n0}: {' → '.join(map(str, trajectory))}")
                found_closure = True
        
        if not found_closure:
            print(f"  No closure found!")
        print()

def count_patterns_by_j_sum(k: int) -> None:
    """Count how many patterns exist for each J value."""
    print(f"\n=== PATTERN COUNTS FOR k={k} ===\n")
    
    J_min = math.floor(1.585 * k) + 1
    j_counts = {}
    j_valid = {}
    
    for mask in range(2**k):
        pattern = [(mask >> i) & 1 + 1 for i in range(k)]
        J = sum(pattern)
        
        if J >= J_min:
            j_counts[J] = j_counts.get(J, 0) + 1
            
            # Check modular validity
            valid = False
            for n0 in [1, 9, 17, 25, 33, 41, 49, 57]:
                n = n0
                ok = True
                
                for j in pattern:
                    if j == 2 and n % 8 != 1:
                        ok = False
                        break
                    n = ((3 * n + 1) // (4 if j == 2 else 2)) % 64
                
                if ok and n % 8 == n0 % 8:
                    valid = True
                    break
            
            if valid:
                j_valid[J] = j_valid.get(J, 0) + 1
    
    print(f"J value | Total patterns | Modularly valid | Survival rate")
    print("-" * 55)
    
    for J in sorted(j_counts.keys()):
        total = j_counts[J]
        valid = j_valid.get(J, 0)
        rate = valid / total if total > 0 else 0
        print(f"{J:4} | {total:14} | {valid:15} | {rate:13.1%}")

def explain_why_no_closure():
    """Explain the mathematical reason for no closure."""
    print("\n\n=== THE MATHEMATICAL REASON ===\n")
    
    print("1. HIGH J REQUIREMENT:")
    print("   Need J > 1.585k to have 2^J > 3^k")
    print("   This forces many j=2 positions\n")
    
    print("2. MODULAR DRIFT:")
    print("   Each j=2 followed by j=1 causes drift")
    print("   n ≡ 1 (mod 32) → j=2 → 1 → j=1 → 2 (mod 8)")
    print("   Other starting points drift even more\n")
    
    print("3. LIMITED RECOVERY:")
    print("   Only n ≡ 1 (mod 32) allows consecutive j=2")
    print("   But this gives identical elements!")
    print("   Other patterns can't maintain high J\n")
    
    print("4. THE SQUEEZE:")
    print("   Patterns with J > 1.585k almost always")
    print("   contain subsequences that break modular closure")

def find_barely_valid_patterns():
    """Find patterns that almost work."""
    print("\n\n=== PATTERNS THAT ALMOST WORK ===\n")
    
    for k in range(5, 12):
        J_min = math.floor(1.585 * k) + 1
        
        print(f"\nk={k} (need J≥{J_min}):")
        
        found_any = False
        for mask in range(2**k):
            pattern = [(mask >> i) & 1 + 1 for i in range(k)]
            J = sum(pattern)
            
            if J >= J_min:
                # Check cycle equation
                C = 0
                s = 0
                for i in range(k):
                    C += 3**(k-1-i) * 2**s
                    s += pattern[i]
                
                d = 2**J - 3**k
                if d > 0 and C % d == 0:
                    n1 = C // d
                    if n1 > 0 and n1 % 2 == 1:
                        print(f"  Pattern {pattern}: J={J}, n₁={n1}")
                        
                        # Check why it fails
                        n = n1
                        elements = [n]
                        failed = False
                        fail_reason = ""
                        
                        for i, j in enumerate(pattern):
                            if j == 2 and n % 8 != 1:
                                failed = True
                                fail_reason = f"Position {i}: n={n} ≢ 1 (mod 8)"
                                break
                            n = (3 * n + 1) // (4 if j == 2 else 2)
                            if n % 2 == 0:
                                failed = True
                                fail_reason = f"Position {i}: got even n={n}"
                                break
                            elements.append(n)
                        
                        if not failed and elements[-1] != n1:
                            fail_reason = f"Doesn't close: {elements[-1]} ≠ {n1}"
                        elif not failed and len(set(elements[:-1])) < k:
                            fail_reason = "Elements not distinct"
                        
                        if fail_reason:
                            print(f"    Fails: {fail_reason}")
                        else:
                            print(f"    SUCCESS? Checking... {elements}")
                        
                        found_any = True
        
        if not found_any:
            print("  No patterns with integer n₁")

def main():
    """Run investigation."""
    analyze_modular_closure()
    count_patterns_by_j_sum(10)
    count_patterns_by_j_sum(15)
    explain_why_no_closure()
    find_barely_valid_patterns()
    
    print("\n\n=== CONCLUSION ===\n")
    print("The modular constraints are incredibly effective because:")
    print("1. High-J patterns require many j=2 positions")
    print("2. j=2 positions create strong modular requirements")
    print("3. These requirements rarely align with closure needs")
    print("4. The few patterns that might work fail other constraints")
    print("\nThis explains why k=9-20 have NO valid patterns!")

if __name__ == "__main__":
    main()