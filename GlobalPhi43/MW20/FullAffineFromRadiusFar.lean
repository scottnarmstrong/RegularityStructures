module

public import GlobalPhi43.MW20.RadiusAffineSeminorm

/-! Full affine norms require both the radius estimate and an actual far-pair bound. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- Radius control alone is not enlarged to a full seminorm. The canonical
coefficient controls the full norm only after far pairs are separately paid. -/
theorem localAffineSeminorm_le_radius_and_far
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (hD : IsOpen D) {γ d H B : ℝ}
    (hγ : 1 < γ) (hd : 0 < d) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hrad : radiusAffineSeminorm U D γ d ≤ ENNReal.ofReal H)
    (hfar : ∀ x ∈ D, ∀ y ∈ D, d < Local.pdist x y →
      |U (x, y) - ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i)| ≤
        B * Local.pdist x y ^ γ) :
    localAffineSeminorm U D γ ≤ ENNReal.ofReal (H + B) := by
  simp only [localAffineSeminorm, iSup_le_iff]
  intro x hx
  apply (iInf_le _ (diagonalSpatialCoefficient U x)).trans
  simp only [affineRemainderSeminorm, iSup_le_iff]
  intro y hy hne
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne hne) γ)).2
  by_cases hxy : Local.pdist x y ≤ d
  · exact (radiusAffineSeminorm_remainder_bound U hU D hD hγ hd hH hrad hx hy hxy hne).trans
      (mul_le_mul_of_nonneg_right (by linarith : H ≤ H + B)
        (Real.rpow_nonneg (Local.pdist_nonneg _ _) γ))
  · exact (hfar x hx y hy (lt_of_not_ge hxy)).trans
      (mul_le_mul_of_nonneg_right (by linarith : B ≤ H + B)
        (Real.rpow_nonneg (Local.pdist_nonneg _ _) γ))

end GlobalPhi43.MW20
