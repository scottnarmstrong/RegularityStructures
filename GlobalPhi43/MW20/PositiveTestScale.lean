module

public import GlobalPhi43.MW20.LargeScalePowerAlgebra
public import GlobalPhi43.MW20.CubicRootScale

/-! Positive-norm smoothing and commutator errors at the actual scale. -/

public section

namespace GlobalPhi43.MW20

/-- A proved parent weighted Holder bound gives the decaying smoothing
error at T=1/(Mk), uniformly over the literal k>2 range. -/
theorem parent_holder_testing_error {M k C H s : ℝ}
    (hM : 0 < M) (hk : 2 < k) (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hH : ((1 / M) * (k - 1) / k) ^ s * H ≤ C * M) :
    H * (((1 / M) / k) ^ s) ≤ C * (2 : ℝ) ^ s * M * k ^ (-s) := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  have hd : 0 < (1 / M) * (k - 1) / k := by positivity
  have hb : H ≤ C * M / (((1 / M) * (k - 1) / k) ^ s) :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hd s)).2 (by simpa only [mul_comm] using hH)
  have hp := reciprocal_depth_power hM hk hs
  have he := reciprocal_testing_power hM hk0 s (1 + s)
  have hexp : 1 + s - s = (1 : ℝ) := by ring
  rw [hexp, Real.rpow_one] at he
  calc
    _ ≤ (C * M / (((1 / M) * (k - 1) / k) ^ s)) * (((1 / M) / k) ^ s) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (C * M * (1 / (((1 / M) * (k - 1) / k) ^ s))) * (((1 / M) / k) ^ s) := by ring
    _ ≤ (C * M * ((2 : ℝ) ^ s * M ^ s)) * (((1 / M) / k) ^ s) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ = C * (2 : ℝ) ^ s * ((((1 / M) / k) ^ s) * M ^ (1 + s)) := by
      rw [Real.rpow_add hM, Real.rpow_one]
      ring
    _ = _ := by rw [he]; ring

end GlobalPhi43.MW20
