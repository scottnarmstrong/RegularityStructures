module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! Reciprocal-amplitude powers for the parent-amplitude closing row. -/

public section

namespace GlobalPhi43.MW20

/-- Exact amplitude and scale powers at T=d0/k and d0=1/M.
This is ordinary scalar algebra, not a scaling statement for Psi. -/
theorem reciprocal_testing_power {M k : ℝ} (hM : 0 < M) (hk : 0 < k) (a b : ℝ) :
    ((1 / M) / k) ^ a * M ^ b = M ^ (b - a) * k ^ (-a) := by
  rw [Real.div_rpow (by positivity : 0 ≤ 1 / M) hk.le,
    Real.div_rpow zero_le_one hM.le, Real.one_rpow,
    Real.rpow_sub hM, Real.rpow_neg hk.le]
  ring

/-- The printed k>2 range gives the depth comparison uniformly. -/
theorem reciprocal_depth_comparison {M k : ℝ} (hM : 0 < M) (hk : 2 < k) :
    1 / (2 * M) ≤ (1 / M) * (k - 1) / k ∧
      (1 / M) * (k - 1) / k ≤ 1 / M := by
  have hk0 : 0 < k := by linarith
  constructor
  · apply (le_div_iff₀ hk0).2
    field_simp
    nlinarith
  · apply (div_le_iff₀ hk0).2
    have hp : 0 < 1 / M := by positivity
    nlinarith

/-- Reciprocal depth powers cost at most the fixed factor 2^s. -/
theorem reciprocal_depth_power {M k s : ℝ} (hM : 0 < M) (hk : 2 < k) (hs : 0 ≤ s) :
    1 / (((1 / M) * (k - 1) / k) ^ s) ≤ (2 : ℝ) ^ s * M ^ s := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  have hd : 0 < (1 / M) * (k - 1) / k := by positivity
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 / (2 * M))
    (reciprocal_depth_comparison hM hk).1 hs
  have hi := one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) s) hp
  apply hi.trans_eq
  rw [Real.div_rpow zero_le_one (by positivity : 0 ≤ 2 * M), Real.one_rpow,
    one_div_one_div, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hM.le]

end GlobalPhi43.MW20
