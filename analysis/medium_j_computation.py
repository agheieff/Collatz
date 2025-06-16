#!/usr/bin/env python3
"""
Computational analysis of medium-J cycles to find the real contradiction
"""

import math

def analyze_medium_j(k, j_ratio):
    """
    Analyze a potential cycle with given k and J/k ratio
    """
    J = int(k * j_ratio)
    
    # Compute denominator
    d = 2**J - 3**k
    d_abs = abs(d)
    
    # Closure constant lower bound (use log to avoid overflow)
    log_C_min = math.log10(0.686) + k * math.log10(4)
    
    # Required n1 (in log scale)
    log_n1_min = log_C_min - math.log10(d_abs) if d_abs > 0 else float('inf')
    
    # Cycle bound
    n_max = 2**k
    
    print(f"\nk = {k}, J/k = {j_ratio:.3f}, J = {J}")
    print(f"Denominator d = 2^{J} - 3^{k}")
    print(f"  d/3^k = {d/3**k:.6e}")
    print(f"  |d| ≈ {d_abs:.3e}")
    print(f"log10(C_min) ≈ {log_C_min:.2f}")
    print(f"log10(n1_min) ≈ {log_n1_min:.2f}")
    print(f"log10(n_max) = log10(2^k) = {k * math.log10(2):.2f}")
    
    log_ratio = log_n1_min - k * math.log10(2)
    print(f"log10(n1_min/n_max) = {log_ratio:.2f}")
    
    if log_ratio > 0:
        print("❌ CONTRADICTION: n1_min > n_max")
    else:
        print("✓ No immediate contradiction")
    
    # Additional analysis for medium-J
    if 1.6 <= j_ratio <= 1.9:
        print("\nMedium-J analysis:")
        # Number of j=1 vs j=2 positions
        n_j1 = 2*k - J
        n_j2 = J - k
        print(f"  Positions with j=1: {n_j1} ({100*n_j1/k:.1f}%)")
        print(f"  Positions with j=2: {n_j2} ({100*n_j2/k:.1f}%)")
        
        # Pattern constraints
        print(f"  Average gap between j=1's: {k/n_j1:.1f}")
        
    return log_ratio > 0

# Test different k values and J ratios
print("=== CRISIS ANALYSIS ===")
for k in [100, 500, 1000]:
    # Near log_2(3) ≈ 1.585
    analyze_medium_j(k, 1.585)
    
print("\n=== MEDIUM-J ANALYSIS ===")
for k in [100, 500, 1000, 2000]:
    for ratio in [1.6, 1.7, 1.8]:
        contradiction = analyze_medium_j(k, ratio)

print("\n=== SEARCHING FOR THE REAL CONSTRAINT ===")

def check_structural_constraint(k, J):
    """
    Check if a given (k,J) pair can support a valid j-sequence structure
    """
    n_j1 = 2*k - J
    n_j2 = J - k
    
    # Can we arrange n_j1 ones among k positions?
    # With modular constraints?
    
    # Simplified check: if j=1 positions must be spread out
    # but j=2 positions need specific mod 8 patterns
    min_gap = k // n_j1 if n_j1 > 0 else k
    
    # If gaps are too large, we get runs of j=2 that create problems
    if min_gap > 5:
        return False, f"Large j=2 runs of length {min_gap}"
    
    # If too many j=1's, pattern becomes impossible
    if n_j1 > k/2:
        return False, f"Too many j=1 positions ({n_j1})"
    
    return True, "Potentially valid"

print("\nStructural feasibility:")
for k in [100, 200, 500, 1000]:
    print(f"\nk = {k}:")
    for ratio in [1.6, 1.65, 1.7, 1.75, 1.8, 1.85]:
        J = int(k * ratio)
        valid, reason = check_structural_constraint(k, J)
        status = "✓" if valid else "❌"
        print(f"  J/k = {ratio:.2f}: {status} {reason}")