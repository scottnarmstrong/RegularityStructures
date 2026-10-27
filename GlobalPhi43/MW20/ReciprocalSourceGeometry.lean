module

public import GlobalPhi43.MW20.LargeScaleTestingGeometry
public import GlobalPhi43.MW20.LargeScalePowerAlgebra

/-! Actual admissible source insets at the reciprocal-amplitude scale. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- All geometric side conditions follow from the source scale range.
The nonempty mixed domain and T<1 are not extra analytic assumptions. -/
theorem reciprocal_source_geometry {r M k : ℝ}
    (hr : 0 ≤ r) (hM : 0 < M) (hk : 2 < k) (hS : r + 1 / M ≤ 1 / 2) :
    let d₀ := 1 / M
    let T := d₀ / k
    let d := d₀ * (k - 1) / k
    0 < T ∧ T < 1 ∧ d ∈ Ioc (0 : ℝ) d₀ ∧ d₀ * M ≤ 1 ∧
      r < 1 / 2 ∧ (Local.cylinderInterior r d).Nonempty := by
  have hk0 : 0 < k := by linarith
  have hd₀ : 0 < 1 / M := by positivity
  have hd := reciprocal_depth_comparison hM hk
  have hdp : 0 < (1 / M) * (k - 1) / k :=
    (by positivity : 0 < 1 / (2 * M)).trans_le hd.1
  obtain ⟨x, hx⟩ := sourceCylinder_nonempty
    (show r + 1 / M ∈ Icc (0 : ℝ) (1 / 2) from ⟨by positivity, hS⟩)
  dsimp only
  refine ⟨by positivity, ?_, ⟨hdp, hd.2⟩, ?_, by linarith, ?_⟩
  · apply (div_lt_iff₀ hk0).2
    linarith
  · exact (one_div_mul_cancel hM.ne').le
  · exact ⟨x, Local.cylinderInterior_mono hdp.le hd.2
      (sourceCylinder_add_subset_mixed hr hd₀.le hx)⟩

end GlobalPhi43.MW20
