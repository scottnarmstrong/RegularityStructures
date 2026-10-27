module

public import GlobalPhi43.MW20.SourceCompleteForcing
public import GlobalPhi43.MW20.ForcingMonomialMajorants
public import GlobalPhi43.MW20.ReciprocalSourceGeometry

/-! Actual W forcing supremum at the reciprocal-amplitude scale. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- The ordinary W budget supplies the actual large-scale forcing supremum.
No separate smoothed-field estimate or regularity premise is assumed. -/
theorem source_W_forcing_sup
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (W : ParabolicSpace → ℝ) {r M k ε c : ℝ}
    (hr : 0 ≤ r) (hM : 0 < M) (hk : 2 < k)
    (hS : r + 1 / M ≤ 1 / 2) (hc : 0 ≤ c)
    (hbudget : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(3 / 2) - 3 * ε) W ≤ ENNReal.ofReal (c * M ^ (3 / 2 - 3 * ε))) :
    let T := (1 / M) / k
    let μ := infiniteKernelMeasure Φ hΦ T
      (div_pos (one_div_pos.mpr hM) (by linarith : 0 < k))
    sourceSup (pastSmooth μ W) (r + 1 / M) ≤
      c * M ^ (3 : ℝ) * k ^ (3 / 2 + 3 * ε) := by
  have hT1 := (reciprocal_source_geometry hr hM hk hS).2.1.le
  have hk0 : 0 < k := by linarith
  have hT : 0 < (1 / M) / k := by positivity
  have hp := source_negative_forcing_sup Φ hΦ W hr
    (show r + 1 / M ∈ Icc (0 : ℝ) (1 / 2) from ⟨by positivity, hS⟩)
    (le_add_of_nonneg_right (by positivity)) hc hM.le hbudget hT hT1
  have he := reciprocal_testing_power hM hk0 (-(3 / 2) - 3 * ε) (3 / 2 - 3 * ε)
  have hexp : (3 / 2 - 3 * ε) - (-(3 / 2) - 3 * ε) = (3 : ℝ) := by ring
  rw [hexp] at he
  dsimp only
  apply hp.trans_eq
  calc
    _ = c * (((1 / M) / k) ^ (-(3 / 2) - 3 * ε) * M ^ (3 / 2 - 3 * ε)) := by ring
    _ = _ := by
      have ha : -(-(3 / 2 : ℝ) - 3 * ε) = 3 / 2 + 3 * ε := by ring
      rw [he, ha]
      ring

end GlobalPhi43.MW20
