module

public import GlobalPhi43.MW20.LargeScaleForcingMonomial

/-! Uniform majorants for the actual parent forcing terms. -/

public section

namespace GlobalPhi43.MW20

/-- A positive-norm forcing monomial at the actual reciprocal scale. -/
theorem parent_forcing_monomial_majorant {M k C a b s q : ℝ}
    (hM : 0 < M) (hk : 2 < k) (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hexp : b + 1 + s - a = 3) (haq : -a ≤ q) :
    ((1 / M) / k) ^ a * M ^ b *
        (C * M / (((1 / M) * (k - 1) / k) ^ s)) ≤
      C * (2 : ℝ) ^ s * (M ^ (3 : ℝ) * k ^ q) := by
  apply (parent_forcing_monomial hM hk hC hs hexp).trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (forcing_scale_power_le hk haq) (by positivity)) (by positivity)

/-- A forcing monomial with no positive norm has the same cubic amplitude. -/
theorem plain_forcing_monomial_majorant {M k a b q : ℝ}
    (hM : 0 < M) (hk : 2 < k) (hexp : b - a = 3) (haq : -a ≤ q) :
    ((1 / M) / k) ^ a * M ^ b ≤ M ^ (3 : ℝ) * k ^ q := by
  rw [reciprocal_testing_power hM (by linarith), hexp]
  exact mul_le_mul_of_nonneg_left (forcing_scale_power_le hk haq) (by positivity)

end GlobalPhi43.MW20
