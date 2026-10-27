module

public import GlobalPhi43.MW20.GlobalRadiusCoefficient
public import GlobalPhi43.MW20.SourceAffineCoefficient
public import GlobalPhi43.Local.SchauderInputs

/-! Full coefficient Holder control for the actual MW20 expansion, from
only the radius-local U norm and truncated scalar Holder norms.
No unrestricted affine norm, independent coefficient field, or infinite
kernel is required. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- The actual selected coefficient satisfies both source estimates from
radius-local source data. The probing radius is at most half the U radius;
far coefficient pairs are controlled by the proved coefficient supremum. -/
theorem source_global_radius_coefficient_bounds
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {R d κ r A B V H : ℝ} (hR : R < 1 / 2) (_hκ : 0 < κ) (hsmall : κ < 1 / 14)
    (hne : (cylinderInterior R d).Nonempty) (hr : 0 < r)
    (hrr : r ≤ 1 / 2 - d) (hrd : r ≤ d / 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hnorm : radiusAffineSeminorm (sourceExpansion v Y Z) (cylinderInterior R d)
      (3 / 2 - 5 * κ) d ≤ ENNReal.ofReal A)
    (hsup : localTwoPointSup (sourceExpansion v Y Z) (cylinderInterior R d) r ≤ ENNReal.ofReal B)
    (hvNorm : radiusHolderSeminorm v (cylinderInterior R d) (1 / 2 - 3 * κ) (d / 2) ≤ ENNReal.ofReal V)
    (hYNorm : radiusHolderSeminorm Y (cylinderInterior R d) (1 - 2 * κ) (d / 2) ≤ ENNReal.ofReal H) :
    BddAbove ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' cylinderInterior R d) ∧
      (1 / 2 : ℝ) * sSup ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' cylinderInterior R d) ≤
        A * r ^ (1 / 2 - 5 * κ) + B / r ∧
      localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) (cylinderInterior R d)
        (1 / 2 - 5 * κ) ≤ ENNReal.ofReal (2 * (2 ^ (3 / 2 - 5 * κ) + 4) *
          (A + 3 * V * H + r ^ (-(3 / 2) + 5 * κ) * B)) := by
  have hh := radius_cylinder_coefficient_bounds_global (sourceExpansion v Y Z)
    (sourceExpansion_contDiff v Y Z hv hY hZ) hR
    (by linarith : 1 < (3 / 2 : ℝ) - 5 * κ) hne hr hrr hrd hA hB (by positivity : 0 ≤ 3 * V * H)
    (by intro x _; exact expansion_diag v Y Z x) hnorm hsup (β := 1 / 2 - 3 * κ)
    (by
      intro x hx z hz y hy hdxz hdzy
      apply expansion_three_point_bound v Y Z x z y hV
      · simpa only [Real.norm_eq_abs, abs_sub_comm] using
          radiusHolderSeminorm_increment_bound v _ _ _ hV hvNorm hx hz hdxz
      · simpa only [Real.norm_eq_abs, abs_sub_comm] using
          radiusHolderSeminorm_increment_bound Y _ _ _ hH hYNorm hz hy hdzy)
  have he₁ : (3 / 2 - 5 * κ) - 1 = 1 / 2 - 5 * κ := by ring
  have he₂ : -(3 / 2 - 5 * κ) = -(3 / 2) + 5 * κ := by ring
  simpa only [sourceAffineCoefficient, he₁, he₂] using hh

end GlobalPhi43.MW20
