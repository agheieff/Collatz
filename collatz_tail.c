#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <gmp.h>

// For Mac: 
// brew install gmp
// gcc -o collatz_tail collatz_tail.c -lgmp -I/opt/homebrew/include -L/opt/homebrew/lib

// Compute tail₂(n) - number of consecutive 1s at the end
int compute_tail2(mpz_t n) {
    if (mpz_even_p(n)) return 0;
    
    int count = 0;
    mpz_t n_copy;
    mpz_init_set(n_copy, n);
    
    while (mpz_odd_p(n_copy)) {
        count++;
        mpz_fdiv_q_2exp(n_copy, n_copy, 1);
    }
    
    mpz_clear(n_copy);
    return count;
}

// Compute ν₂(n)
int compute_nu2(mpz_t n) {
    if (mpz_odd_p(n)) return 0;
    return mpz_scan1(n, 0);
}

// Analyze a sequence and collect specific statistics
void analyze_for_cycle_theory(mpz_t start, const char* test_name, int max_steps) {
    mpz_t n, three_n_plus_1;
    mpz_init_set(n, start);
    mpz_init(three_n_plus_1);
    
    printf("\n=== %s ===\n", test_name);
    printf("Start magnitude: ~10^%zu\n", mpz_sizeinbase(start, 10));
    printf("Start mod 4: %lu\n", mpz_fdiv_ui(start, 4));
    printf("Start tail₂: %d\n", compute_tail2(start));
    
    // Key statistics
    int j1_count = 0, j2_count = 0;
    int max_tail2 = 0;
    int max_run_length = 0;
    int current_run = 0;
    int total_forced_positions = 0;
    int large_tail_count = 0;  // Count of positions with tail₂ ≥ 10
    
    // Track first 100 j-values for pattern analysis
    int j_pattern[100];
    int tail_pattern[100];
    
    for (int step = 0; step < max_steps && mpz_cmp_ui(n, 1) > 0; step++) {
        int tail2 = compute_tail2(n);
        
        mpz_mul_ui(three_n_plus_1, n, 3);
        mpz_add_ui(three_n_plus_1, three_n_plus_1, 1);
        int j = compute_nu2(three_n_plus_1);
        
        if (step < 100) {
            j_pattern[step] = j;
            tail_pattern[step] = tail2;
        }
        
        // Update statistics
        if (j == 1) {
            j1_count++;
            if (current_run > max_run_length) max_run_length = current_run;
            current_run = 0;
        } else if (j == 2) {
            j2_count++;
            current_run++;
        }
        
        if (tail2 > max_tail2) max_tail2 = tail2;
        if (tail2 >= 10) large_tail_count++;
        
        // Count forced positions
        if (mpz_fdiv_ui(n, 4) == 1 && tail2 >= 4) {
            total_forced_positions += tail2/2;
        }
        
        // Apply Collatz step
        mpz_fdiv_q_2exp(n, three_n_plus_1, j);
    }
    
    // Results
    double j1_percent = 100.0 * j1_count / (j1_count + j2_count);
    printf("\nResults after %d steps:\n", j1_count + j2_count);
    printf("j=1: %d (%.1f%%), j=2: %d (%.1f%%)\n", 
           j1_count, j1_percent, j2_count, 100-j1_percent);
    printf("Target for cycles: j=1 should be ~41.5%%\n");
    printf("Max tail₂: %d\n", max_tail2);
    printf("Max j=2 run: %d\n", max_run_length);
    printf("Positions with tail₂≥10: %d\n", large_tail_count);
    printf("Total forced j=2 positions: %d\n", total_forced_positions);
    
    // Print first part of pattern
    printf("\nFirst 50 positions (j,tail₂):\n");
    for (int i = 0; i < 50 && i < j1_count + j2_count; i++) {
        printf("(%d,%d) ", j_pattern[i], tail_pattern[i]);
        if (i % 10 == 9) printf("\n");
    }
    printf("\n");
    
    mpz_clear(n);
    mpz_clear(three_n_plus_1);
}

// Test specific hypotheses
int main() {
    mpz_t n;
    mpz_init(n);
    
    printf("=== COLLATZ TAIL₂ ANALYSIS FOR CYCLE IMPOSSIBILITY ===\n");
    printf("Testing key predictions about binary Collatz cycles\n");
    
    // Test 1: Does large tail₂ create forced runs?
    printf("\n\n====== TEST GROUP 1: FORCED RUN HYPOTHESIS ======\n");
    printf("Theory: If n ≡ 1 (mod 4) with tail₂(n) = t, next t/2 positions have j=2\n");
    
    mpz_set_ui(n, 1);
    mpz_mul_2exp(n, n, 40);
    mpz_sub_ui(n, n, 1);  // 2^40 - 1 (has tail₂ = 40)
    analyze_for_cycle_theory(n, "Test 1a: 2^40-1 (tail₂=40)", 100);
    
    mpz_set_ui(n, 1);
    mpz_mul_2exp(n, n, 60);
    mpz_sub_ui(n, n, 1);  // 2^60 - 1 
    analyze_for_cycle_theory(n, "Test 1b: 2^60-1 (tail₂=60)", 100);
    
    // Test 2: What happens with huge numbers ≡ 1 (mod 4)?
    printf("\n\n====== TEST GROUP 2: LARGE NUMBER BEHAVIOR ======\n");
    printf("Theory: Large numbers show rigid j-patterns incompatible with ~41.5%% j=1\n");
    
    // Simulate n_min ~ 10^40
    mpz_set_str(n, "1234567890123456789012345678901234567891", 10);  // ~10^40, ends in 1
    analyze_for_cycle_theory(n, "Test 2a: ~10^40 ending in 1", 300);
    
    // Number that's 1 mod 4 with moderate tail₂
    mpz_set_str(n, "9999999999999999999999999999999999999997", 10);  // ≡ 1 (mod 4)
    analyze_for_cycle_theory(n, "Test 2b: ~10^40 with ≡ 1 (mod 4)", 300);
    
    // Test 3: Simulate potential cycle elements
    printf("\n\n====== TEST GROUP 3: SIMULATED CYCLE ELEMENTS ======\n");
    printf("Theory: Elements of form C/d have special structure\n");
    
    // Simulate n = C/d where d = 3^k * small
    mpz_set_str(n, "123456789", 10);
    mpz_mul_2exp(n, n, 119);  // × 2^119 to simulate denominator crisis
    mpz_set_ui(n, 1);
    mpz_mul_2exp(n, n, 133);  // 2^133
    mpz_add_ui(n, n, 15);     // Make it 15 mod 16 (so tail₂ = 4)
    analyze_for_cycle_theory(n, "Test 3a: Simulated C/d structure", 300);
    
    // Test 4: Check j=1 percentage for various starting points
    printf("\n\n====== TEST GROUP 4: J-DISTRIBUTION ANALYSIS ======\n");
    printf("Question: Do large numbers naturally achieve ~41.5%% j=1?\n");
    
    for (int i = 0; i < 5; i++) {
        mpz_set_ui(n, 9);
        for (int j = 0; j < 35 + i*5; j++) {
            mpz_mul_ui(n, n, 10);
        }
        mpz_add_ui(n, n, 2*i + 1);  // Different endings
        
        char test_name[100];
        sprintf(test_name, "Test 4%c: ~10^%d", 'a'+i, 36+i*5);
        analyze_for_cycle_theory(n, test_name, 500);
    }
    
    // Test 5: Special investigation of run patterns
    printf("\n\n====== TEST GROUP 5: RUN PATTERN INVESTIGATION ======\n");
    printf("Question: How do j=2 runs distribute? Are they too long?\n");
    
    // Number with specific binary pattern
    mpz_set_str(n, "FFFFFFFF000000001", 16);  // Mix of 1s and 0s
    mpz_mul_2exp(n, n, 100);
    mpz_add_ui(n, n, 1);
    analyze_for_cycle_theory(n, "Test 5: Structured binary pattern", 200);
    
    // Summary
    printf("\n\n====== SUMMARY FOR CYCLE IMPOSSIBILITY ======\n");
    printf("Key questions this data addresses:\n");
    printf("1. Do large tail₂ values create forced j=2 runs? [Check Test Group 1]\n");
    printf("2. Do huge numbers achieve ~41.5%% j=1 needed for cycles? [Check Test Groups 2,4]\n");
    printf("3. Are j=2 runs too long when numbers are large? [Check Test Group 5]\n");
    printf("4. Do simulated cycle elements show special patterns? [Check Test Group 3]\n");
    
    mpz_clear(n);
    return 0;
}
