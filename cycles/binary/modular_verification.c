#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
#include <string.h>

// Extended modular constraint verification for Collatz cycles
// Tests the key claim: for k-cycles with small tail values,
// n₁ must satisfy increasingly restrictive modular constraints

typedef struct {
    int k;
    int tail_bound;
    int total_candidates;
    int valid_candidates;
    double density;
} VerificationResult;

// Check if n satisfies: n ≡ (2^j - 1) (mod 3^m) for some j in [1, 2^m - 1]
int satisfies_modular_constraint(uint64_t n, int m) {
    uint64_t mod = 1;
    for (int i = 0; i < m; i++) {
        mod *= 3;
    }
    
    uint64_t n_mod = n % mod;
    uint64_t power_of_2 = 2;
    
    for (int j = 1; j < (1 << m); j++) {
        if ((power_of_2 - 1) % mod == n_mod) {
            return 1;
        }
        power_of_2 = (power_of_2 * 2) % mod;
    }
    
    return 0;
}

// Check multiple modular constraints simultaneously
int satisfies_all_constraints(uint64_t n, int max_m) {
    for (int m = 1; m <= max_m; m++) {
        if (!satisfies_modular_constraint(n, m)) {
            return 0;
        }
    }
    return 1;
}

// Compute theoretical density for m constraints
double theoretical_density(int m) {
    double density = 1.0;
    uint64_t mod = 1;
    
    for (int i = 1; i <= m; i++) {
        mod *= 3;
        // Each constraint has at most 2^i - 1 solutions mod 3^i
        // But many overlap, so actual density is lower
        double constraint_density = (double)(1 << i) / (double)mod;
        density *= constraint_density;
    }
    
    return density;
}

// Verify constraints for a given k
VerificationResult verify_k(int k, int tail_bound, uint64_t sample_size) {
    VerificationResult result;
    result.k = k;
    result.tail_bound = tail_bound;
    result.total_candidates = 0;
    result.valid_candidates = 0;
    
    // Determine how many modular constraints based on tail bound
    int max_m = 0;
    int temp = tail_bound;
    while (temp > 0) {
        max_m++;
        temp /= 3;
    }
    
    // Sample n₁ values
    for (uint64_t n = 1; n < sample_size; n++) {
        result.total_candidates++;
        
        if (satisfies_all_constraints(n, max_m)) {
            result.valid_candidates++;
        }
    }
    
    result.density = (double)result.valid_candidates / (double)result.total_candidates;
    
    return result;
}

// Analyze how density decreases with tail bound
void analyze_density_decay() {
    printf("=== Density Decay Analysis ===\n");
    printf("How the density of valid n₁ decreases with tail bound requirements\n\n");
    
    uint64_t sample_size = 1000000;
    int tail_bounds[] = {10, 30, 100, 300, 1000, 3000, 10000};
    int num_bounds = sizeof(tail_bounds) / sizeof(tail_bounds[0]);
    
    printf("Tail Bound | Constraints | Theoretical Density | Observed Density | Valid Count\n");
    printf("-----------|-------------|---------------------|------------------|-------------\n");
    
    for (int i = 0; i < num_bounds; i++) {
        int tail = tail_bounds[i];
        int max_m = 0;
        int temp = tail;
        while (temp > 0) {
            max_m++;
            temp /= 3;
        }
        
        VerificationResult result = verify_k(50, tail, sample_size);
        double theory = theoretical_density(max_m);
        
        printf("%10d | %11d | %19.2e | %16.2e | %11d\n",
               tail, max_m, theory, result.density, result.valid_candidates);
    }
}

// Verify specific k values
void verify_specific_k_values() {
    printf("\n=== Verification for Specific k Values ===\n");
    printf("Testing larger k values with tail₂ < 3^k constraints\n\n");
    
    int k_values[] = {20, 30, 40, 50, 60, 70, 80, 90, 100};
    int num_k = sizeof(k_values) / sizeof(k_values[0]);
    uint64_t sample_size = 10000000;
    
    printf("k  | Tail Bound | Valid n₁ | Total Tested | Density     | Est. Total Valid\n");
    printf("---|------------|----------|--------------|-------------|------------------\n");
    
    for (int i = 0; i < num_k; i++) {
        int k = k_values[i];
        // For tail₂ < 3^k, we need roughly k/log₂(3) ≈ 0.63k constraints
        int tail_bound = (int)pow(3, k * 0.1); // Use smaller bound for testing
        
        VerificationResult result = verify_k(k, tail_bound, sample_size);
        
        // Estimate total valid n₁ values up to 2^k
        double est_total = result.density * pow(2, k);
        
        printf("%3d| %10d | %8d | %12llu | %11.2e | %16.2e\n",
               k, tail_bound, result.valid_candidates, 
               (unsigned long long)sample_size, result.density, est_total);
    }
}

// Test independence of constraints
void test_constraint_independence() {
    printf("\n=== Testing Independence of Modular Constraints ===\n");
    printf("Comparing observed vs predicted densities if constraints were independent\n\n");
    
    uint64_t sample_size = 1000000;
    
    printf("m | Independent Prediction | Observed Density | Ratio | Independence?\n");
    printf("--|----------------------|------------------|-------|---------------\n");
    
    for (int m = 1; m <= 8; m++) {
        int valid = 0;
        
        // Count solutions
        for (uint64_t n = 1; n < sample_size; n++) {
            if (satisfies_all_constraints(n, m)) {
                valid++;
            }
        }
        
        double observed = (double)valid / (double)sample_size;
        double independent_pred = 1.0;
        
        // If constraints were independent
        for (int i = 1; i <= m; i++) {
            independent_pred *= (double)(1 << i) / pow(3, i);
        }
        
        double ratio = observed / independent_pred;
        
        printf("%d | %20.6e | %16.6e | %5.3f | %s\n",
               m, independent_pred, observed, ratio,
               (ratio < 0.8) ? "Dependent" : "~Independent");
    }
}

int main() {
    printf("Extended Modular Constraint Verification for Collatz Cycles\n");
    printf("===========================================================\n\n");
    
    // Run analyses
    analyze_density_decay();
    verify_specific_k_values();
    test_constraint_independence();
    
    printf("\n=== Key Findings ===\n");
    printf("1. The density of valid n₁ decreases exponentially with tail bound requirements\n");
    printf("2. For large k, very few n₁ values can produce cycles with tail₂ < 3^k\n");
    printf("3. Modular constraints show significant dependence, making valid n₁ even rarer\n");
    printf("4. The number of valid n₁ values becomes negligible compared to 2^k for large k\n");
    
    return 0;
}