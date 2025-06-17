#!/usr/bin/env python3
"""
Derive and verify the cycle equation step by step.
This will help us complete the Lean proof.
"""

def derive_cycle_equation():
    """Derive the cycle equation from first principles."""
    
    print("=== CYCLE EQUATION DERIVATION ===\n")
    
    print("Starting with a k-cycle: n₁ → n₂ → ... → nₖ → n₁\n")
    
    print("Step 1: Write the cycle relations")
    print("  n₂ = (3n₁ + 1) / 2^j₁")
    print("  n₃ = (3n₂ + 1) / 2^j₂")
    print("  ...")
    print("  n₁ = (3nₖ + 1) / 2^jₖ")
    
    print("\nStep 2: Clear denominators")
    print("  2^j₁ × n₂ = 3n₁ + 1")
    print("  2^j₂ × n₃ = 3n₂ + 1")
    print("  ...")
    print("  2^jₖ × n₁ = 3nₖ + 1")
    
    print("\nStep 3: Telescope the equations")
    print("Multiply equation i by 3^(k-i) and 2^(J₀+...+Jᵢ₋₁):")
    print("  (Equation 1) × 3^(k-1):")
    print("    3^(k-1) × 2^j₁ × n₂ = 3^k × n₁ + 3^(k-1)")
    print("  (Equation 2) × 3^(k-2) × 2^j₁:")
    print("    3^(k-2) × 2^(j₁+j₂) × n₃ = 3^(k-1) × 2^j₁ × n₂ + 3^(k-2) × 2^j₁")
    
    print("\nStep 4: Add all equations")
    print("Left side telescopes to: 2^J × n₁ (where J = j₁ + ... + jₖ)")
    print("Right side: 3^k × n₁ + Σᵢ 3^(k-1-i) × 2^(j₁+...+jᵢ)")
    
    print("\nStep 5: Rearrange")
    print("  2^J × n₁ = 3^k × n₁ + C")
    print("  n₁ × (2^J - 3^k) = C")
    print("\nwhere C = Σᵢ₌₀^(k-1) 3^(k-1-i) × 2^(j₁+...+jᵢ)")

def verify_with_example():
    """Verify the equation with the trivial cycle."""
    
    print("\n\n=== VERIFICATION WITH k=1 CYCLE ===\n")
    
    k = 1
    n1 = 1
    j1 = 2
    
    print(f"Cycle: {{{n1}}} with j = {j1}")
    
    # Calculate C
    C = 3**(k-1) * 2**0  # Only one term
    print(f"\nC = 3^0 × 2^0 = {C}")
    
    # Calculate denominator
    J = j1
    denom = 2**J - 3**k
    print(f"2^J - 3^k = 2^{J} - 3^{k} = {2**J} - {3**k} = {denom}")
    
    # Verify equation
    print(f"\nVerification:")
    print(f"  n₁ × (2^J - 3^k) = {n1} × {denom} = {n1 * denom}")
    print(f"  C = {C}")
    print(f"  Equal? {n1 * denom == C} ✓")

def analyze_c_structure():
    """Analyze the structure of C for different patterns."""
    
    print("\n\n=== STRUCTURE OF C ===\n")
    
    print("C = Σᵢ₌₀^(k-1) 3^(k-1-i) × 2^(s_i)")
    print("where s_i = j₁ + j₂ + ... + jᵢ\n")
    
    # Example patterns
    patterns = [
        (3, [2, 1, 2], "212"),
        (4, [2, 2, 2, 1], "2221"),
        (5, [2, 1, 2, 1, 2], "21212")
    ]
    
    for k, j_seq, pattern_str in patterns:
        print(f"\nPattern {pattern_str} (k={k}):")
        
        C = 0
        s = 0
        terms = []
        
        for i in range(k):
            term = 3**(k-1-i) * 2**s
            C += term
            terms.append(f"3^{k-1-i} × 2^{s}")
            s += j_seq[i]
        
        print(f"  C = {' + '.join(terms)}")
        print(f"    = {' + '.join(str(3**(k-1-i) * 2**(sum(j_seq[:i]))) for i in range(k))}")
        print(f"    = {C}")
        
        J = sum(j_seq)
        print(f"  J = {J}")
        print(f"  Need to check if C is divisible by |2^{J} - 3^{k}|")

def telescoping_example():
    """Show telescoping with a concrete example."""
    
    print("\n\n=== TELESCOPING EXAMPLE ===\n")
    
    print("Consider k=3 with pattern j₁=2, j₂=1, j₃=2:\n")
    
    print("Equations:")
    print("  2² × n₂ = 3n₁ + 1")
    print("  2¹ × n₃ = 3n₂ + 1") 
    print("  2² × n₁ = 3n₃ + 1")
    
    print("\nMultiply and telescope:")
    print("  (Eq 1) × 3²:        3² × 2² × n₂ = 3³ × n₁ + 3²")
    print("  (Eq 2) × 3¹ × 2²:  3¹ × 2³ × n₃ = 3² × 2² × n₂ + 3¹ × 2²")
    print("  (Eq 3) × 3⁰ × 2³:  3⁰ × 2⁵ × n₁ = 3¹ × 2³ × n₃ + 3⁰ × 2³")
    
    print("\nAdd all equations:")
    print("  Left side: 2⁵ × n₁")
    print("  Right side: 3³ × n₁ + (3² + 3¹ × 2² + 3⁰ × 2³)")
    print("            = 3³ × n₁ + (9 + 12 + 8)")
    print("            = 27 × n₁ + 29")
    
    print("\nFinal equation:")
    print("  32 × n₁ = 27 × n₁ + 29")
    print("  5 × n₁ = 29")
    print("  n₁ = 29/5 (not an integer!)")
    print("\nThis confirms no 3-cycle with pattern 212 exists!")

def main():
    """Run all derivations and verifications."""
    
    derive_cycle_equation()
    verify_with_example()
    analyze_c_structure()
    telescoping_example()
    
    print("\n\n=== KEY INSIGHTS FOR LEAN PROOF ===\n")
    print("1. The telescoping is mechanical - multiply equation i by appropriate powers")
    print("2. C has a specific structure as a sum")
    print("3. The cycle equation n₁(2^J - 3^k) = C must have integer solutions")
    print("4. This gives strong divisibility constraints")

if __name__ == "__main__":
    main()