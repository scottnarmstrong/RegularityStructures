module

public import GlobalPhi43.MW20.RadiusAffineSeminorm
public import GlobalPhi43.MW20.SourceConeEstimate

/-!
# Coefficient supremum from only the actual radius-local affine norm
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ContDiff

/-- The coefficient supremum uses no three-point hypothesis or unrestricted
remainder norm. Its only test pairs have exactly the probing radius r. -/
theorem radius_cone_coefficient_sup
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (hD : IsOpen D) (hne : D.Nonempty)
    {γ L r₀ r A B : ℝ} (hγ : 1 < γ) (hL : 0 < L) (hr : 0 < r)
    (hrr : r ≤ r₀) (hrL : r ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hnorm : radiusAffineSeminorm U D γ L ≤ ENNReal.ofReal A)
    (hsup : localTwoPointSup U D r ≤ ENNReal.ofReal B)
    (hcone : SpatialInteriorCone D r₀ (1 / 2)) :
    BddAbove ((fun x => ‖diagonalSpatialCoefficient U x‖) '' D) ∧
      (1 / 2 : ℝ) * sSup ((fun x => ‖diagonalSpatialCoefficient U x‖) '' D) ≤
        A * r ^ (γ - 1) + B / r := by
  apply cone_estimate_sup D hne (diagonalSpatialCoefficient U)
    (fun x y => U (x, y)) (fun a x y => ∑ j, a j * (y.2 j - x.2 j)) pdist hr
    (by norm_num) (hcone r hr hrr)
  · intro x hx y hy hd
    have hne' : y ≠ x := by
      intro he; subst y
      have hz : pdist x x = 0 := by simp only [pdist, sub_self, abs_zero,
        Real.sqrt_zero, norm_zero, max_self]
      rw [hz] at hd
      linarith
    simpa only [hd] using radiusAffineSeminorm_remainder_bound U hU D hD
      hγ hL hA hnorm hx hy (hd.le.trans hrL) hne'
  · intro x hx y hy hd
    exact localTwoPointSup_bound U D r hB hsup hx hy hd.le

end GlobalPhi43.MW20
