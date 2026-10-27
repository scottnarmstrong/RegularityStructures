module

public import GlobalPhi43.MW20.CubicRootScale

/-! Exact normalization of the three actual forcing cube roots. -/

public section

namespace GlobalPhi43.MW20

/-- The cubic parent amplitude becomes exactly M, retaining the full
smallness and scale factor under the cube root. -/
theorem cubic_forcing_root_normalization {D K c M k q : ℝ}
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hc : 0 ≤ c) (hM : 0 < M) (hk : 0 < k)
    (hbound : D ≤ K * c * M ^ (3 : ℝ) * k ^ q) :
    D ^ (1 / 3 : ℝ) ≤ K ^ (1 / 3 : ℝ) * M * (c * k ^ q) ^ (1 / 3 : ℝ) := by
  have hDcube : (D ^ (1 / 3 : ℝ)) ^ 3 = D := by
    simpa using rpow_third_cube hD 1
  have hKcube : (K ^ (1 / 3 : ℝ)) ^ 3 = K := by
    simpa using rpow_third_cube hK 1
  have hck : 0 ≤ c * k ^ q := by positivity
  have hckcube : ((c * k ^ q) ^ (1 / 3 : ℝ)) ^ 3 = c * k ^ q := by
    simpa using rpow_third_cube hck 1
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hD _)
    (by positivity : 0 ≤ K ^ (1 / 3 : ℝ) * M * (c * k ^ q) ^ (1 / 3 : ℝ))
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [hDcube, mul_pow, mul_pow, hKcube, hckcube]
  rw [show M ^ (3 : ℝ) = M ^ (3 : ℕ) from Real.rpow_natCast M 3] at hbound
  convert hbound using 1; ring

end GlobalPhi43.MW20
