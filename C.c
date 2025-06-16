#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <float.h>

#define MAX_K 40
#define ALPHA 0.41504077640085654  // 2 - log₂(3)

// Structure to store results for each k
typedef struct {
    int k;
    int n1;
    long double min_C;
    long double C_over_4k;  // C / 4^k ratio
    long double C_minus_3k_over_4k;  // (C - 3^k) / 4^k ratio
    int positions[MAX_K];
    int critical_n1;  // n1 value closest to α*k
    long double critical_d;  // denominator at critical n1
    long double critical_ratio;  // C/d at critical point
} Result;

// Compute power efficiently using long double
long double power_ld(long double base, int exp) {
    long double result = 1.0L;
    long double b = base;
    while (exp > 0) {
        if (exp & 1) result *= b;
        b *= b;
        exp >>= 1;
    }
    return result;
}

// Compute C for given positions of j=1
long double compute_C(int k, int n1, int* positions) {
    long double C = power_ld(4.0L, k) - power_ld(3.0L, k);
    
    for (int i = 0; i < n1; i++) {
        int p = positions[i];
        long double term = power_ld(3.0L, k - p) * power_ld(2.0L, 2*p - i - 2);
        C -= term;
    }
    
    return C;
}

// Generate next combination
int next_combination(int* positions, int n1, int k) {
    int i = n1 - 1;
    while (i >= 0 && positions[i] == k - n1 + i + 1) {
        i--;
    }
    
    if (i < 0) return 0;  // No more combinations
    
    positions[i]++;
    for (int j = i + 1; j < n1; j++) {
        positions[j] = positions[i] + j - i;
    }
    
    return 1;
}

// Analyze patterns for a specific k
Result analyze_k(int k) {
    Result res;
    res.k = k;
    res.min_C = LDBL_MAX;
    res.C_over_4k = 0;
    res.C_minus_3k_over_4k = 0;
    
    int n1_max = (int)(k * ALPHA);
    long double pow4k = power_ld(4.0L, k);
    long double pow3k = power_ld(3.0L, k);
    
    // Find critical n1 (closest to α*k)
    res.critical_n1 = (int)round(k * ALPHA);
    if (res.critical_n1 > n1_max) res.critical_n1 = n1_max;
    
    printf("\nAnalyzing k=%d (n1_max=%d, critical_n1=%d)\n", k, n1_max, res.critical_n1);
    
    // For each possible n1
    for (int n1 = 1; n1 <= n1_max; n1++) {
        int positions[MAX_K];
        long double min_C_for_n1 = LDBL_MAX;
        int best_positions[MAX_K];
        
        // Initialize first combination
        for (int i = 0; i < n1; i++) {
            positions[i] = i + 1;
        }
        
        // Check all combinations
        int count = 0;
        do {
            long double C = compute_C(k, n1, positions);
            count++;
            
            if (C < min_C_for_n1) {
                min_C_for_n1 = C;
                memcpy(best_positions, positions, n1 * sizeof(int));
            }
        } while (next_combination(positions, n1, k));
        
        // Update global minimum for this k
        if (min_C_for_n1 < res.min_C) {
            res.min_C = min_C_for_n1;
            res.n1 = n1;
            res.C_over_4k = min_C_for_n1 / pow4k;
            res.C_minus_3k_over_4k = (min_C_for_n1 - pow3k) / pow4k;
            memcpy(res.positions, best_positions, n1 * sizeof(int));
        }
        
        // Special handling for critical n1
        if (n1 == res.critical_n1) {
            // Compute denominator d = 3^k * (2^(αk - n1) - 1)
            long double exponent = ALPHA * k - n1;
            long double d = pow3k * (powl(2.0L, exponent) - 1.0L);
            res.critical_d = d;
            res.critical_ratio = min_C_for_n1 / d;
            
            printf("  n1=%d: min_C=%.6Le, C/4^k=%.6Lf, (C-3^k)/4^k=%.6Lf (checked %d configs)\n", 
                   n1, min_C_for_n1, min_C_for_n1/pow4k, (min_C_for_n1-pow3k)/pow4k, count);
            printf("    Critical analysis: d=%.6Le, C/d=%.6Le\n", d, res.critical_ratio);
        }
        
        // Print progress for some n1 values
        if (n1 <= 5 || n1 == n1_max || abs(n1 - res.critical_n1) <= 1) {
            printf("  n1=%d: min_C=%.6Le, C/4^k=%.6Lf, (C-3^k)/4^k=%.6Lf (checked %d configs)\n", 
                   n1, min_C_for_n1, min_C_for_n1/pow4k, (min_C_for_n1-pow3k)/pow4k, count);
        }
    }
    
    return res;
}

// Print summary table
void print_summary(Result* results, int num_results) {
    printf("\n=== SUMMARY TABLE ===\n");
    printf("k\tn1_min\tC_min/4^k\t(C_min-3^k)/4^k\tCritical_n1\tC/d_critical\tExtr_Positions\n");
    printf("------------------------------------------------------------------------------------\n");
    
    for (int i = 0; i < num_results; i++) {
        Result* r = &results[i];
        printf("%d\t%d\t%.6Lf\t%.6Lf\t%d\t\t%.3Le\t", 
               r->k, r->n1, r->C_over_4k, r->C_minus_3k_over_4k, 
               r->critical_n1, r->critical_ratio);
        
        // Print first few positions
        printf("{");
        for (int j = 0; j < (r->n1 < 5 ? r->n1 : 5); j++) {
            printf("%d", r->positions[j]);
            if (j < r->n1 - 1) printf(",");
        }
        if (r->n1 > 5) printf(",...");
        printf("}\n");
    }
    
    // Look for patterns in C/4^k ratio
    printf("\n=== ANALYSIS OF C/4^k RATIOS ===\n");
    long double min_ratio = 1.0;
    for (int i = 0; i < num_results; i++) {
        if (results[i].C_over_4k < min_ratio) {
            min_ratio = results[i].C_over_4k;
        }
    }
    printf("Minimum C/4^k ratio found: %.8Lf\n", min_ratio);
    
    // Check if ratio is decreasing
    printf("\nTrend analysis of C/4^k:\n");
    for (int i = 1; i < num_results; i++) {
        long double change = results[i].C_over_4k - results[i-1].C_over_4k;
        printf("k=%d to k=%d: change = %+.8Lf\n", 
               results[i-1].k, results[i].k, change);
    }
    
    // Analyze critical ratios
    printf("\n=== DENOMINATOR CRISIS ANALYSIS ===\n");
    printf("k\tδ={αk}\t\td_approx/3^k\tC/d\n");
    printf("------------------------------------------------\n");
    for (int i = 0; i < num_results; i++) {
        Result* r = &results[i];
        double fractional_part = ALPHA * r->k - floor(ALPHA * r->k);
        long double d_over_3k = r->critical_d / power_ld(3.0L, r->k);
        printf("%d\t%.6f\t%.6Le\t%.3Le\n", 
               r->k, fractional_part, d_over_3k, r->critical_ratio);
    }
}

int main() {
    printf("=== Collatz Closure Constant C Analysis ===\n");
    printf("Testing formula: C = 4^k - 3^k - Σ[3^(k-p_i) * 2^(2p_i-i-1)]\n");
    printf("Alpha = %.15f\n\n", ALPHA);
    
    Result results[MAX_K];
    int num_results = 0;
    
    // Analyze k from 3 to MAX_K
    for (int k = 3; k <= MAX_K && k <= 25; k++) {  // Limited to 25 for reasonable runtime
        results[num_results++] = analyze_k(k);
        
        // Also test some specific larger k values where {αk} is small
        if (k == 25) {
            // Add some hand-picked values where denominator crisis occurs
            int special_k[] = {41, 58, 70, 91};  // These have small {αk}
            for (int i = 0; i < 4; i++) {
                if (special_k[i] <= MAX_K) {
                    printf("\n*** Special case: k=%d (small fractional part) ***\n", special_k[i]);
                    results[num_results++] = analyze_k(special_k[i]);
                }
            }
        }
    }
    
    // Print summary
    print_summary(results, num_results);
    
    // Final analysis
    printf("\n=== KEY OBSERVATIONS ===\n");
    printf("1. Look for minimum value of C/4^k across all k\n");
    printf("2. Check if (C-3^k)/4^k approaches a positive constant\n");
    printf("3. Examine C/d ratios during denominator crisis\n");
    printf("4. Note position patterns that minimize C\n");
    
    return 0;
}
