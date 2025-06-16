#!/usr/bin/env python3
"""
Final analysis of medium-J contradictions using logarithmic arithmetic
"""

import math

def log_denominator(k, J):
    """Compute log10(|2^J - 3^k|)"""
    # 2^J - 3^k = 3^k(2^(J-k*log2(3)) - 1)
    alpha = 2 - math.log(3)/math.log(2)  # ≈ 0.415
    
    # J ≈ k * log2(3) means 2^J ≈ 3^k
    ratio = J/k
    if abs(ratio - math.log(3)/math.log(2)) < 0.01:
        # Near crisis - use more careful calculation
        x = J - k * math.log(3)/math.log(2)
        # For small x: 2^x - 1 ≈ x * ln(2)
        if abs(x) < 1:
            log_d = k * math.log10(3) + math.log10(abs(x * math.log(2)))
        else:
            log_d = k * math.log10(3) + math.log10(abs(2**x - 1))
    else:
        # Far from crisis
        log_2J = J * math.log10(2)
        log_3k = k * math.log10(3)
        if log_2J > log_3k:
            log_d = log_2J + math.log10(1 - 10**(log_3k - log_2J))
        else:
            log_d = log_3k + math.log10(1 - 10**(log_2J - log_3k))
    
    return log_d

def analyze_cycle_possibility(k, j_ratio):
    """Check if a cycle with given k and J/k ratio is possible"""
    J = int(k * j_ratio)
    
    # Closure constant: C ≥ 0.686 × 4^k
    log_C = math.log10(0.686) + k * math.log10(4)
    
    # Denominator
    log_d = log_denominator(k, J)
    
    # Required n1 = C/d
    log_n1 = log_C - log_d
    
    # Maximum allowed
    log_n_max = k * math.log10(2)
    
    # Check contradiction
    contradiction = log_n1 > log_n_max
    
    print(f"\nk={k}, J/k={j_ratio:.3f}")
    print(f"  log10(C) ≈ {log_C:.1f}")
    print(f"  log10(|d|) ≈ {log_d:.1f}")
    print(f"  log10(n1) ≈ {log_n1:.1f}")
    print(f"  log10(2^k) = {log_n_max:.1f}")
    print(f"  n1/2^k ≈ 10^{log_n1 - log_n_max:.1f}")
    
    if contradiction:
        print("  ❌ CONTRADICTION!")
    else:
        # Check structural constraints
        n_j1 = 2*k - J
        n_j2 = J - k
        print(f"  ✓ No size contradiction")
        print(f"  j=1 positions: {n_j1} ({100*n_j1/k:.1f}%)")
        print(f"  j=2 positions: {n_j2} ({100*n_j2/k:.1f}%)")
        
        # Check pattern feasibility
        if n_j2 > 0.9 * k:
            print("  ⚠️  High-J: modular incompatibility likely")
        elif n_j1 > 0.4 * k:
            print("  ⚠️  Many j=1s: structural constraints apply")
            
    return contradiction

print("=== TESTING SPECIFIC J/k RATIOS ===")

# Test crisis points
print("\n--- Near Crisis (J ≈ 1.585k) ---")
for k in [100, 1000, 10000]:
    analyze_cycle_possibility(k, 1.585)
    analyze_cycle_possibility(k, 1.586)

# Test medium-J
print("\n--- Medium-J Analysis ---")
for k in [1000, 2000, 5000]:
    for ratio in [1.60, 1.65, 1.70, 1.75, 1.80, 1.85]:
        analyze_cycle_possibility(k, ratio)

# Find the critical threshold
print("\n=== FINDING CRITICAL THRESHOLD ===")

def find_threshold(k):
    """Binary search for the J/k ratio where contradiction appears"""
    low, high = 1.585, 1.6
    
    while high - low > 0.0001:
        mid = (low + high) / 2
        J = int(k * mid)
        log_C = math.log10(0.686) + k * math.log10(4)
        log_d = log_denominator(k, J)
        log_n1 = log_C - log_d
        log_n_max = k * math.log10(2)
        
        if log_n1 > log_n_max:
            high = mid
        else:
            low = mid
    
    return mid

print("\nCritical J/k ratios where contradiction appears:")
for k in [1000, 2000, 5000, 10000]:
    threshold = find_threshold(k)
    print(f"k={k}: J/k ≈ {threshold:.6f}")