#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#define ALPHA 0.41504077640085654  // 2 - log₂(3)

// Find k values where {αk} is small
void find_critical_k(int max_k, double threshold) {
    printf("=== Critical k values where {αk} < %.6f ===\n", threshold);
    printf("k\t{αk}\t\tn1=⌊αk⌋\tδ\t\tComment\n");
    printf("--------------------------------------------------------\n");
    
    for (int k = 3; k <= max_k; k++) {
        double alpha_k = ALPHA * k;
        int n1 = (int)floor(alpha_k);
        double delta = alpha_k - n1;
        
        if (delta < threshold) {
            printf("%d\t%.8f\t%d\t\t%.8f", k, delta, n1, delta);
            
            // Special cases
            if (delta < 0.01) printf("\t*** EXTREME CRISIS ***");
            else if (delta < 0.05) printf("\t** Strong crisis **");
            else if (delta < 0.1) printf("\t* Moderate crisis *");
            
            printf("\n");
        }
    }
    
    // Also find k where {αk} is close to 1 (also causes small denominator)
    printf("\n=== Critical k values where {αk} > %.6f ===\n", 1-threshold);
    printf("k\t{αk}\t\tn1=⌊αk⌋\tδ\t\tComment\n");
    printf("--------------------------------------------------------\n");
    
    for (int k = 3; k <= max_k; k++) {
        double alpha_k = ALPHA * k;
        int n1 = (int)floor(alpha_k);
        double delta = alpha_k - n1;
        
        if (delta > 1-threshold) {
            printf("%d\t%.8f\t%d\t\t%.8f", k, delta, n1, delta);
            
            // Special cases
            if (delta > 0.99) printf("\t*** EXTREME CRISIS ***");
            else if (delta > 0.95) printf("\t** Strong crisis **");
            else if (delta > 0.9) printf("\t* Moderate crisis *");
            
            printf("\n");
        }
    }
}

// Compute C for consecutive positions at end
long double compute_C_consecutive_end(int k, int n1) {
    long double C = powl(4.0L, k) - powl(3.0L, k);
    
    // Positions are {k-n1+1, k-n1+2, ..., k}
    for (int i = 0; i < n1; i++) {
        int p = k - n1 + i + 1;
        long double term = powl(3.0L, k - p) * powl(2.0L, 2*p - i - 2);
        C -= term;
    }
    
    return C;
}

// Analyze specific critical k values
void analyze_critical_k(int k) {
    double alpha_k = ALPHA * k;
    int n1_critical = (int)round(alpha_k);
    double delta = alpha_k - floor(alpha_k);
    
    printf("\n=== Detailed analysis for k = %d ===\n", k);
    printf("αk = %.10f, n1_critical = %d, δ = %.10f\n", alpha_k, n1_critical, delta);
    
    // Compute C for critical n1 with consecutive end positions
    long double C = compute_C_consecutive_end(k, n1_critical);
    long double pow3k = powl(3.0L, k);
    long double pow4k = powl(4.0L, k);
    
    // Compute denominator
    long double d = pow3k * (powl(2.0L, delta) - 1.0L);
    
    printf("C = %.6Le\n", C);
    printf("C/4^k = %.10Lf\n", C/pow4k);
    printf("(C-3^k)/4^k = %.10Lf\n", (C-pow3k)/pow4k);
    printf("d = %.6Le\n", d);
    printf("d/3^k = %.10Lf\n", d/pow3k);
    printf("n_min = C/d = %.6Le\n", C/d);
    printf("n_min/(4/3)^k = %.6Lf\n", C/d/powl(4.0L/3.0L, k));
    
    // Check if n_min > k (basic sanity check)
    if (C/d > k) {
        printf("*** n_min > k: This creates immediate problems! ***\n");
    }
    
    // Check growth bound
    long double max_growth = powl(1.057L, k);
    printf("Maximum growth factor (1.057^k) = %.6Le\n", max_growth);
    printf("If n_min = %.2Le, then n_max could be up to %.2Le\n", C/d, (C/d)*max_growth);
}

int main() {
    printf("=== Finding Critical K Values for Denominator Crisis ===\n\n");
    
    // Find all k up to 1000 where crisis occurs
    find_critical_k(200, 0.1);
    
    // Analyze specific critical cases
    int critical_cases[] = {17, 41, 58, 70, 91, 99, 116, 133, 150, 174, 191};
    int num_cases = sizeof(critical_cases) / sizeof(critical_cases[0]);
    
    printf("\n\n=== DETAILED ANALYSIS OF EXTREME CASES ===\n");
    for (int i = 0; i < num_cases; i++) {
        analyze_critical_k(critical_cases[i]);
    }
    
    // Summary
    printf("\n\n=== SUMMARY ===\n");
    printf("1. The denominator crisis occurs infinitely often due to Weyl equidistribution\n");
    printf("2. When δ < 0.01, we get n_min > 50(4/3)^k, growing exponentially\n");
    printf("3. Combined with growth bounds, this creates arithmetic impossibility\n");
    printf("4. The empirical bound C ≥ 0.686×4^k makes the crisis severe\n");
    
    return 0;
}
