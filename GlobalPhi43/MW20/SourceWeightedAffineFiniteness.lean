module

public import GlobalPhi43.MW20.SourceAffineFiniteness

/-! Weighted affine norms on the original source cylinders. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff ENNReal

/-- A single compact Taylor bound controls all insets and all cutoffs.
The data-dependent constant proves finiteness only. -/
theorem source_expansion_uniform_radius_bound
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r γ : ℝ} (hr : 0 ≤ r) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 ≤ d → ∀ L : ℝ,
      radiusAffineSeminorm (sourceExpansion v Y Z) (Local.cylinderInterior r d) γ L ≤
        ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := parabolic_affine_remainder_finite_bound
    (sourceExpansion v Y Z) (sourceExpansion_contDiff v Y Z hv hY hZ) 1 hγ hγ2
  refine ⟨C, hC, fun d hd L => ?_⟩
  apply radiusAffineSeminorm_le_of_remainder_bound _ _
    (diagonalSpatialCoefficient (sourceExpansion v Y Z)) γ L C
  intro x hx y hy _ _
  have hdiag : sourceExpansion v Y Z (x, x) = 0 := Local.expansion_diag v Y Z x
  simpa only [hdiag, sub_zero] using
    hb x (mixedInterior_subset_unit_closedBall hr hd hx)
      y (mixedInterior_subset_unit_closedBall hr hd hy)

end GlobalPhi43.MW20
