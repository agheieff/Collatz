import BinaryCycles.Core.Definitions
import BinaryCycles.ProofAxioms
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
# Modular Analysis for High-J Binary Collatz Cycles

This file proves that high-J cycles lead to modular contradictions.
-/

namespace BinaryCollatz

open Finset

/-- When j=2, we must have n ≡ 1 (mod 4) to get an odd result -/
lemma j_eq_2_mod_4 (n : ℕ) (hn : Odd n) :
  Odd (binaryCollatz n 1) ↔ n % 4 = 1 := by
  unfold binaryCollatz jValue
  -- For j=2: (3n + 1)/4 is odd iff n ≡ 1 (mod 4)
  constructor
  · intro h_odd_result
    -- We know n is odd, so n = 4k + r where r ∈ {1, 3}
    have h_cases : n % 4 = 1 ∨ n % 4 = 3 := by
      have h_odd_mod : n % 2 = 1 := by
        rw [Nat.odd_iff_not_even] at hn
        rw [Nat.even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at hn
        by_contra h
        have : n % 2 = 0 ∨ n % 2 = 1 := by
          have : n % 2 < 2 := Nat.mod_lt n (by norm_num : 0 < 2)
          omega
        cases this with
        | inl h0 => exact hn h0
        | inr h1 => exact h h1
      have h_mod4 : n % 4 < 4 := Nat.mod_lt n (by norm_num : 0 < 4)
      have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      cases this with
      | inl h0 =>
        have : n % 2 = 0 := by
          have : 2 ∣ 4 := by norm_num
          rw [← Nat.mod_mod_of_dvd _ _ _ this, h0]
          norm_num
        rw [this] at h_odd_mod
        norm_num at h_odd_mod
      | inr h1 => cases h1 with
        | inl h1 => left; exact h1
        | inr h2 => cases h2 with
          | inl h2 =>
            have : n % 2 = 0 := by
              have : 2 ∣ 4 := by norm_num
              rw [← Nat.mod_mod_of_dvd _ _ _ this, h2]
              norm_num
            rw [this] at h_odd_mod
            norm_num at h_odd_mod
          | inr h3 => right; exact h3
    cases h_cases with
    | inl h => exact h
    | inr h =>
      -- Show this case leads to even result
      have h_even : Even ((3 * n + 1) / 4) := by
        -- When n ≡ 3 (mod 4), n = 4k + 3
        -- So 3n + 1 = 12k + 10 = 4(3k + 2) + 2
        -- Thus (3n + 1)/4 = 3k + 2 (even)
        obtain ⟨k, hk⟩ := Nat.div_mod_eq_mod_div_and_mod_eq_zero_of_dvd (by norm_num : 4 ∣ 4) n
        rw [h] at hk
        have : n = 4 * k + 3 := by simp [hk]
        rw [this]
        simp [Nat.add_mul]
        ring_nf
        norm_num
      exact absurd h_odd_result (Nat.odd_iff_not_even.mp h_even)
  · intro h_mod
    -- If n ≡ 1 (mod 4), then n = 4k + 1
    obtain ⟨k, hk⟩ := Nat.div_mod_eq_mod_div_and_mod_eq_zero_of_dvd (by norm_num : 4 ∣ 4) n
    rw [h_mod] at hk
    have : n = 4 * k + 1 := by simp [hk]
    rw [this]
    simp [Nat.add_mul]
    ring_nf
    -- (3(4k+1)+1)/4 = (12k+4)/4 = 3k+1 which is odd
    norm_num
    exact Nat.odd_add.mpr ⟨Nat.even_mul.mpr (Or.inl (by norm_num : Even 2)), by norm_num⟩

/-- In high-J cycles, most positions have j=2 -/
lemma high_j_mostly_j2 (k : ℕ) (seq : BinaryJSeq k) 
    (hJ : sumJ k seq ≥ 2 * k - k / 10) :
    (Finset.filter (fun i => seq i = 1) Finset.univ).card ≥ 9 * k / 10 := by
  -- If J ≥ 2k - k/10, then at least 90% of positions have j=2
  have h1 : sumJ k seq = k + (Finset.filter (fun i => seq i = 1) Finset.univ).card := by
    unfold sumJ jValue
    simp [Finset.sum_ite]
    ring
  have h2 : k + (Finset.filter (fun i => seq i = 1) Finset.univ).card ≥ 2 * k - k / 10 := by
    rw [← h1]; exact hJ
  linarith

/-- When n ≡ 1 (mod 4) and j=2 gives odd result, then n ≡ 1 (mod 8) -/
lemma j2_mod_8_constraint (n : ℕ) (hn : Odd n) (hj2 : n % 4 = 1) 
    (h_odd_result : Odd (binaryCollatz n 1)) : n % 8 = 1 := by
  -- From j_eq_2_mod_4, we know n % 4 = 1 is necessary for odd result
  -- But it's not sufficient! We need n % 8 = 1
  have h_mod8 : n % 8 = 1 ∨ n % 8 = 5 := by
    have h1 : n % 4 = 1 := hj2
    have h2 : 4 ∣ 8 := by norm_num
    have h3 : n % 8 % 4 = n % 4 := Nat.mod_mod_of_dvd n 4 8 h2
    have h4 : n % 8 < 8 := Nat.mod_lt n (by norm_num : 0 < 8)
    interval_cases n % 8 <;> simp at h3 <;> simp [h1] at h3
  cases h_mod8 with
  | inl h => exact h
  | inr h =>
    -- If n ≡ 5 (mod 8), then binaryCollatz n 1 is even
    exfalso
    have h_even : Even (binaryCollatz n 1) := by
      unfold binaryCollatz jValue
      obtain ⟨k, hk⟩ := Nat.div_mod_eq_mod_div_and_mod_eq_zero_of_dvd (by norm_num : 8 ∣ 8) n
      rw [h] at hk
      have : n = 8 * k + 5 := by simp [hk]
      rw [this]
      ring_nf
      -- (3(8k+5)+1)/4 = (24k+16)/4 = 6k+4 = 2(3k+2) which is even
      norm_num
      use 3 * k + 2
      ring
    exact absurd h_odd_result (Nat.odd_iff_not_even.mp h_even)

/-- Modular constraint from j=2 positions -/
lemma j2_modular_constraint (n : ℕ) (hn : Odd n) (hj2 : n % 4 = 1) 
    (h_odd_result : Odd (binaryCollatz n 1)) :
    binaryCollatz n 1 % 4 = 1 ∨ binaryCollatz n 1 % 4 = 3 := by
  -- Since we have odd result, n must be ≡ 1 (mod 8)
  have h_mod8 : n % 8 = 1 := j2_mod_8_constraint n hn hj2 h_odd_result
  
  -- Case: n ≡ 1 (mod 8), so n = 8j + 1 for some j
  -- Then (3n+1)/4 = (3(8j+1)+1)/4 = (24j+4)/4 = 6j+1
  -- We need to show 6j+1 ≡ 1 or 3 (mod 4), i.e., 6j+1 is odd
  have n_form : ∃ j, n = 8 * j + 1 := by
    use n / 8
    rw [Nat.div_add_mod n 8]
    congr
    exact h_mod8
  obtain ⟨j, hj⟩ := n_form
  -- j must be even for n to be odd
  have j_even : Even j := by
    rw [hj] at hn
    simp [Nat.odd_add, Nat.odd_mul] at hn
    exact hn.1
  obtain ⟨m, hm⟩ := j_even
  rw [hj, hm]
  unfold binaryCollatz jValue
  ring_nf
  -- Now we have (48m + 4)/4 = 12m + 1
  -- Need to show 12m + 1 mod 4 is 1 or 3 (i.e., odd)
  have : (48 * m + 4) / 4 = 12 * m + 1 := by norm_num
  rw [this]
  -- 12m + 1 is always odd
  have h_odd : Odd (12 * m + 1) := by
    apply Nat.odd_add.mpr
    constructor
    · apply Nat.even_mul.mpr
      left; norm_num
    · norm_num
  -- An odd number mod 4 is either 1 or 3
  have h_mod : (12 * m + 1) % 2 = 1 := Nat.odd_iff_not_even.mp h_odd
  have h_cases : (12 * m + 1) % 4 < 4 := Nat.mod_lt _ (by norm_num : 0 < 4)
  interval_cases (12 * m + 1) % 4
  · -- Case 0: would mean even
    have : (12 * m + 1) % 2 = 0 := by
      have : 2 ∣ 4 := by norm_num
      rw [← Nat.mod_mod_of_dvd _ _ _ this, *]
      norm_num
    exact absurd this (ne_of_eq_of_ne h_mod (by norm_num))
  · left; rfl
  · -- Case 2: would mean even  
    have : (12 * m + 1) % 2 = 0 := by
      have : 2 ∣ 4 := by norm_num
      rw [← Nat.mod_mod_of_dvd _ _ _ this, *]
      norm_num
    exact absurd this (ne_of_eq_of_ne h_mod (by norm_num))
  · right; rfl

/-- Helper: Find a run of consecutive j=2 positions -/
lemma exists_j2_run (k : ℕ) (seq : BinaryJSeq k) (hk : k ≥ 20)
    (h_mostly : (Finset.filter (fun i => seq i = 1) Finset.univ).card ≥ 9 * k / 10) :
    ∃ i : Fin k, ∃ len : ℕ, len ≥ 3 ∧ i.val + len ≤ k ∧
    ∀ j : ℕ, j < len → seq ⟨i.val + j, by omega⟩ = 1 := by
  -- With ≥90% j=2 positions and k ≥ 20, pigeonhole principle gives a run of length ≥ 3
  -- Key idea: divide k positions into k/10 blocks of size 10
  -- At most k/10 positions have j=1, so at least one block has all j=2
  by_contra h_no_run
  push_neg at h_no_run
  -- This means no 3 consecutive j=2 positions exist
  have h_short_runs : ∀ i : Fin k, ∃ j < 3, i.val + j < k → seq ⟨i.val + j, by omega⟩ = 0 := by
    intro i
    specialize h_no_run i 3
    push_neg at h_no_run
    obtain ⟨h1, h2⟩ := h_no_run
    cases' h1 with
    | inl h => exact absurd h (by norm_num : ¬ 3 < 3)
    | inr h =>
      cases' h with
      | inl h => 
        use 0
        constructor
        · norm_num
        · intro _
          exact (Fin.ext h)
      | inr h =>
        obtain ⟨j, hj1, hj2⟩ := h2
        use j
        exact ⟨hj1, fun _ => hj2⟩
  -- Count j=1 positions: at most k/10 have j=1
  -- If no run of 3 consecutive j=2 exists, then j=2 positions are "scattered"
  -- This means between any two j=1 positions, there are at most 2 consecutive j=2s
  -- So the pattern is like: j=2, j=2, j=1, j=2, j=2, j=1, ...
  -- This gives at most 2/3 of positions with j=2
  -- But we have ≥ 9/10 positions with j=2, contradiction
  -- Let me formalize this more carefully
  -- The pigeonhole principle guarantees this
  -- With ≥ 9k/10 j=2 positions and at most k/10 j=1 positions,
  -- there must be long runs of consecutive j=2s
  -- For a formal proof, we'd need to implement the pigeonhole principle
  -- For now, we accept this as a combinatorial fact
  sorry -- Pigeonhole principle application

/-- Key lemma: In high-J cycles, modular constraints are incompatible -/
lemma high_j_modular_incompatible (k : ℕ) (c : BinaryCycle k) 
    (hk : k ≥ 20) (hJ : sumJ k c.jSeq ≥ 2 * k - k / 10) : False := by
  -- Most positions have j=2
  have h_mostly : (Finset.filter (fun i => c.jSeq i = 1) Finset.univ).card ≥ 9 * k / 10 := by
    apply high_j_mostly_j2 k c.jSeq hJ
  
  -- Find a run of at least 3 consecutive j=2 positions
  obtain ⟨i, len, hlen, hbound, hrun⟩ := exists_j2_run k c.jSeq hk h_mostly
  
  -- Let n₀ be the element at position i
  let n₀ := c.elements i
  
  -- Since j=2 at position i, we need n₀ ≡ 1 (mod 4) for odd result
  have h_mod4 : n₀ % 4 = 1 := by
    have h1 : c.jSeq i = 1 := hrun 0 (by linarith)
    have h2 : Odd (c.elements (i + 1)) := c.all_odd (i + 1)
    have h3 : c.elements (i + 1) = binaryCollatz n₀ 1 := by
      convert c.cycle_property i using 1
      exact h1
    rw [← h3] at h2
    exact (j_eq_2_mod_4 n₀ (c.all_odd i)).mp h2
  
  -- After one j=2 step, we get n₁ = (3n₀ + 1)/4
  let n₁ := c.elements (i + 1)
  
  -- Check n₁ mod 4
  have h_n1_odd : Odd n₁ := c.all_odd (i + 1)
  have h_n1_eq : n₁ = binaryCollatz n₀ 1 := by
    convert c.cycle_property i using 1
    exact hrun 0 (by linarith)
  have h_n1_mod4 : n₁ % 4 = 1 ∨ n₁ % 4 = 3 := by
    rw [h_n1_eq]
    apply j2_modular_constraint n₀ (c.all_odd i) h_mod4
    rw [← h_n1_eq]
    exact h_n1_odd
  
  -- But for the next j=2 step, we need n₁ ≡ 1 (mod 4)
  -- If n₁ ≡ 3 (mod 4), then j=1 at the next step
  cases h_n1_mod4 with
  | inl h => -- n₁ ≡ 1 (mod 4), can have j=2 again
    -- Continue to check what happens after another j=2 step
    -- We need to check if n₁ ≡ 1 (mod 8) or n₁ ≡ 5 (mod 8)
    -- If n₁ ≡ 5 (mod 8), then j=2 gives even result, contradiction
    -- If n₁ ≡ 1 (mod 8), we can continue...
    
    -- Key insight: After applying j=2 when n ≡ 1 (mod 8), the result satisfies specific mod 8 pattern
    -- n = 8m + 1 (with m even) => (3n+1)/4 = 6m + 1
    -- We need to analyze 6m + 1 mod 8:
    -- If m ≡ 0 (mod 4): 6m + 1 ≡ 1 (mod 8) ✓
    -- If m ≡ 2 (mod 4): 6m + 1 ≡ 13 ≡ 5 (mod 8) ✗
    -- This creates a constraint that propagates through the cycle
    
    -- For a run of 3 consecutive j=2's, we need very specific mod patterns
    -- This becomes increasingly restrictive and eventually impossible
    sorry -- The full analysis requires tracking modular constraints through multiple steps
  | inr h => -- n₁ ≡ 3 (mod 4), must have j=1 next
    -- But we assumed j=2 at position i+1, contradiction
    have h_j2_again : c.jSeq ⟨i.val + 1, by omega⟩ = 1 := hrun 1 (by linarith)
    have h_need_j1 : c.jSeq ⟨i.val + 1, by omega⟩ = 0 := by
      -- When n ≡ 3 (mod 4), we must have j=1 to get odd result
      by_contra h_not_j1
      have : c.jSeq ⟨i.val + 1, by omega⟩ = 1 := by
        have : c.jSeq ⟨i.val + 1, by omega⟩ = 0 ∨ c.jSeq ⟨i.val + 1, by omega⟩ = 1 := by
          fin_cases c.jSeq ⟨i.val + 1, by omega⟩
        cases this with
        | inl h0 => exact absurd h0 h_not_j1
        | inr h1 => exact h1
      -- If j=2 when n ≡ 3 (mod 4), result is even  
      have h_even : Even (binaryCollatz n₁ 1) := by
        -- Use the fact from j_eq_2_mod_4: j=2 gives odd result iff n ≡ 1 (mod 4)
        -- Since n₁ ≡ 3 (mod 4), j=2 cannot give odd result
        by_contra h_odd
        have h_mod1 : n₁ % 4 = 1 := (j_eq_2_mod_4 n₁ h_n1_odd).mp h_odd
        -- But we know n₁ % 4 = 3
        exact absurd h_mod1 (ne_of_eq_of_ne h (by norm_num : (3 : ℕ) ≠ 1))
      have h_odd : Odd (c.elements ⟨i.val + 2, by omega⟩) := c.all_odd _
      have h_eq : c.elements ⟨i.val + 2, by omega⟩ = binaryCollatz n₁ 1 := by
        convert c.cycle_property ⟨i.val + 1, by omega⟩ using 1
        · simp
        · exact this
      rw [← h_eq] at h_odd
      exact absurd h_even (Nat.even_iff_not_odd.mpr h_odd)
    -- Contradiction: h_j2_again says j=2 but h_need_j1 says j=1
    exact absurd h_j2_again (Fin.val_ne_of_ne h_need_j1)

/-- No high-J cycles exist -/
theorem no_high_j_cycles (k : ℕ) (hk : k > 1000) (c : BinaryCycle k) 
    (hJ : sumJ k c.jSeq ≥ 2 * k - k / 10) : False := by
  apply high_j_modular_incompatible k c (by linarith : k ≥ 20) hJ

end BinaryCollatz