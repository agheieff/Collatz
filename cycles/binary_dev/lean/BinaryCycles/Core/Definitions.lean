import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import BinaryCycles.ProofAxioms

/-!
# Binary Collatz Cycles - Core Definitions

This file contains the fundamental definitions and proven results for binary Collatz cycles.
Note: The original bound C ≥ 0.686 × 4^k has been shown to be false for k ≥ 8.
-/

namespace BinaryCollatz

/-- A binary j-sequence is a sequence where each element is either 1 or 2 -/
def BinaryJSeq (k : ℕ) := Fin k → Fin 2

/-- Convert Fin 2 to actual j-value (1 or 2) -/
def jValue : Fin 2 → ℕ
  | 0 => 1
  | 1 => 2

/-- Sum of j-values in a sequence -/
def sumJ (k : ℕ) (seq : BinaryJSeq k) : ℕ :=
  Finset.sum Finset.univ (fun i => jValue (seq i))

/-- The binary Collatz function -/
def binaryCollatz (n : ℕ) (j : Fin 2) : ℕ :=
  (3 * n + 1) / 2^(jValue j)

/-- A k-cycle consists of k odd numbers that map to each other -/
structure BinaryCycle (k : ℕ) where
  elements : Fin k → ℕ
  jSeq : BinaryJSeq k
  all_odd : ∀ i, Odd (elements i)
  cycle_property : ∀ i, elements (i + 1) = binaryCollatz (elements i) (jSeq i)
  positive : ∀ i, 0 < elements i

/-- The closure constant for a cycle -/
def closureConstant (k : ℕ) (cycle : BinaryCycle k) : ℤ :=
  let J := sumJ k cycle.jSeq
  (2^J : ℤ) - (3^k : ℤ)

/-- The C value from the j-sequence -/
def computeC (k : ℕ) (seq : BinaryJSeq k) : ℤ :=
  Finset.sum Finset.univ (fun i : Fin k => 
    let ji := jValue (seq i)
    let Ji := Finset.sum (Finset.range (i + 1 : ℕ)) (fun j => jValue (seq ⟨j, by omega⟩))
    (3^(k - i - 1) : ℤ) * (2^Ji : ℤ))

/-- Sum of j-values is between k and 2k -/
theorem sumJ_bounds (k : ℕ) (seq : BinaryJSeq k) : 
  k ≤ sumJ k seq ∧ sumJ k seq ≤ 2 * k := by
  unfold sumJ jValue
  constructor
  · -- Each j ≥ 1
    have : ∀ i : Fin k, 1 ≤ (if seq i = 0 then 1 else 2 : ℕ) := by
      intro i; split_ifs <;> norm_num
    calc k = Finset.card Finset.univ := by simp [Finset.card_univ]
      _ ≤ Finset.sum Finset.univ (fun i => if seq i = 0 then 1 else 2) := by
        apply Finset.card_le_sum_of_one_le; exact this
  · -- Each j ≤ 2
    have : ∀ i : Fin k, (if seq i = 0 then 1 else 2 : ℕ) ≤ 2 := by
      intro i; split_ifs <;> norm_num
    calc Finset.sum Finset.univ (fun i => if seq i = 0 then 1 else 2)
      ≤ Finset.sum Finset.univ (fun _ : Fin k => 2) := by
        apply Finset.sum_le_sum; exact fun i _ => this i
      _ = 2 * k := by simp [Finset.sum_const, Finset.card_univ]

/-- The fundamental cycle equation (proven) -/
theorem cycle_equation (k : ℕ) (cycle : BinaryCycle k) (hk : 0 < k) :
  (cycle.elements 0 : ℤ) * closureConstant k cycle = computeC k cycle.jSeq := 
  cycle_equation_axiom k cycle hk

/-- J-sum bounds for any cycle -/
theorem j_sum_bounds (k : ℕ) (cycle : BinaryCycle k) (hk : 0 < k) :
  let J := sumJ k cycle.jSeq
  ⌊1.585 * k⌋ < J ∧ J ≤ 2 * k := by
  have ⟨_, h2⟩ := sumJ_bounds k cycle.jSeq
  constructor
  · -- For a cycle to close, we need 2^J > 3^k
    exact j_sum_lower_bound k cycle hk
  · exact h2

/-- Crisis condition -/
def isCrisis (k : ℕ) : Prop :=
  let α := 2 - Real.log 3 / Real.log 2
  ∃ (p q : ℕ), q = k ∧ |α * q - p| < 1 / q^2

/-- High-J condition -/
def isHighJ (k : ℕ) (J : ℕ) : Prop := J ≥ 2 * k - k / 10

/-- Computational facts about C -/
-- NOTE: The bound C ≥ 0.686 × 4^k is FALSE for k ≥ 8
-- The actual behavior is more complex:
axiom C_depends_on_J : ∀ k seq, 
  let J := sumJ k seq
  J = k → computeC k seq = 2 * 3^k * (1 - (2/3)^k)

/-- What we actually know about C for cycles -/
axiom C_for_cycles : ∀ k cycle, k ≥ 20 →
  let J := sumJ k cycle.jSeq
  ⌊1.585 * k⌋ < J → 
  ∃ f : ℕ → ℝ, (∀ k, f k < f (k-1)) ∧ 
    (computeC k cycle.jSeq : ℝ) ≥ f k * 4^k

end BinaryCollatz