module

public import GlobalPhi43.MW20.CubicRootScale

/-! Cubic commutator control from the actual parent smoothing error. -/

public section

namespace GlobalPhi43.MW20

/-- A parent Holder testing error pays the complete cubic commutator
scale, with its precise decaying k exponent. -/
theorem commutator_scale_from_parent_error {m M H T s B k : ℝ}
    (hm : 0 ≤ m) (hM : 0 < M) (hmM : m ≤ M) (hH : 0 ≤ H)
    (hT : 0 ≤ T) (hk : 0 < k) (hB : 0 ≤ B)
    (herror : H * T ^ s ≤ B * M * k ^ (-s)) :
    cubicCommutatorScale m H T s ≤ B ^ (1 / 3 : ℝ) * M * k ^ (-s / 3) := by
  have hleft : 0 ≤ cubicCommutatorScale m H T s := by
    unfold cubicCommutatorScale
    positivity
  have hcube : (cubicCommutatorScale m H T s) ^ 3 = T ^ s * m ^ 2 * H := by
    have hmroot : (m ^ (2 / 3 : ℝ)) ^ 3 = m ^ 2 := by
      simpa using rpow_third_cube hm 2
    have hHroot : (H ^ (1 / 3 : ℝ)) ^ 3 = H := by
      simpa using rpow_third_cube hH 1
    simp only [cubicCommutatorScale, mul_pow, rpow_third_cube hT, hmroot, hHroot]
  have hBroot : (B ^ (1 / 3 : ℝ)) ^ 3 = B := by
    simpa using rpow_third_cube hB 1
  have hkroot : (k ^ (-s / 3)) ^ 3 = k ^ (-s) := rpow_third_cube hk.le (-s)
  have hsq : m ^ 2 ≤ M ^ 2 := by nlinarith
  have hh := mul_le_mul hsq herror (by positivity : 0 ≤ H * T ^ s) (sq_nonneg M)
  apply (pow_le_pow_iff_left₀ hleft
    (by positivity : 0 ≤ B ^ (1 / 3 : ℝ) * M * k ^ (-s / 3))
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [hcube, mul_pow, mul_pow, hBroot, hkroot]
  nlinarith only [hh]

end GlobalPhi43.MW20
