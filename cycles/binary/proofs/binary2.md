Theorem 1 (Fundamental Constraints)
For any binary k-cycle with n₁ positions having j=1:

Sum constraint: k·log₂(3) < 2k - n₁ < 2k
Closure equation: n₁ = C/d where d = 3^k(2^(αk-n₁) - 1)
Growth bound: n_max/n_min ≤ (3/2)^{n₁}·(3/4)^{k-n₁}

Proof: Already established rigorously in previous work. □

Theorem 2 (Denominator Bounds)
For any binary k-cycle:
(a) If |n₁ - αk| ≥ 1, then d ≥ 3^k·(2-1) = 3^k
(b) If |n₁ - ⌊αk⌋| ≤ 1, then d ≤ 3^k·(2^{1+δ} - 1) where δ = {αk}
Proof:
(a) If n₁ ≤ αk - 1, then αk - n₁ ≥ 1, so 2^(αk-n₁) ≥ 2, giving d ≥ 3^k.
If n₁ ≥ αk + 1, then J = 2k - n₁ ≤ 2k - αk - 1 = k·log₂(3) - 1 < k·log₂(3), violating the sum constraint.
(b) Direct calculation from d = 3^k(2^(αk-n₁) - 1). □
