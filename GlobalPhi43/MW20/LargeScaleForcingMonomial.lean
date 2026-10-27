module

public import GlobalPhi43.MW20.LargeScalePowerAlgebra

/-! Parent forcing monomials at the actual reciprocal-amplitude scale. -/

public section

namespace GlobalPhi43.MW20

/-- Substituting a proved parent positive-norm bound keeps the cubic
amplitude and costs only a fixed depth-comparison factor. -/
theorem parent_forcing_monomial {M k C a b s : ℝ}
    (hM : 0 < M) (hk : 2 < k) (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hexp : b + 1 + s - a = 3) :
    ((1 / M) / k) ^ a * M ^ b *
        (C * M / (((1 / M) * (k - 1) / k) ^ s)) ≤
      C * (2 : ℝ) ^ s * (M ^ (3 : ℝ) * k ^ (-a)) := by
  have hk0 : 0 < k := by linarith
  have hp := reciprocal_depth_power hM hk hs
  calc
    _ = (C * (((1 / M) / k) ^ a * M ^ (b + 1))) *
        (1 / (((1 / M) * (k - 1) / k) ^ s)) := by
      rw [Real.rpow_add hM b 1, Real.rpow_one]
      ring
    _ ≤ (C * (((1 / M) / k) ^ a * M ^ (b + 1))) * ((2 : ℝ) ^ s * M ^ s) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = C * (2 : ℝ) ^ s * (((1 / M) / k) ^ a * M ^ (b + 1 + s)) := by
      rw [Real.rpow_add hM (b + 1) s]
      ring
    _ = _ := by rw [reciprocal_testing_power hM hk0, hexp]

/-- A finite list of scale exponents can be replaced by its common
majorant without changing the amplitude or making c depend on data. -/
theorem forcing_scale_power_le {k p q : ℝ} (hk : 2 < k) (hpq : p ≤ q) :
    k ^ p ≤ k ^ q := Real.rpow_le_rpow_of_exponent_le (by linarith) hpq

end GlobalPhi43.MW20
