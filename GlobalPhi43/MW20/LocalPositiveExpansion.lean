module

public import GlobalPhi43.MW20.LocalPositiveHolder
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.LocalSourceHolder
public import Mathlib.Basic.ENNReal.Real
public import GlobalPhi43.MW20.SourceConeEstimate
public import GlobalPhi43.MW20.ParentScaleAlgebra
public import GlobalPhi43.MW20.SourceAffineCoefficient
public import GlobalPhi43.Local.RadiusSourceSize

/-! Parent-amplitude two-point and radius bounds from local positive-tree norms. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

theorem source_expansion_parent_two_point_positive {v Y Z : ParabolicSpace → ℝ}
    (hv : SourceCubicRegularity v) {r d α β c : ℝ}
    (hr : 0 ≤ r) (hd : 0 < d) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * sourceSup v r ^ β))
    (hZ : parabolicHolderSeminorm α (parabolicClosedNbhd mwCylinder 1) Z ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 + α))) :
    localTwoPointSup (fun p => Local.expansion v Y Z p.1 p.2)
      (Local.cylinderInterior r d) d ≤ ENNReal.ofReal
        (2 * sourceSup v r + c * d ^ α * sourceSup v r ^ (1 + α) +
          3 * c * d ^ β * sourceSup v r ^ (1 + β)) := by
  have hM := sourceSup_nonneg_of_continuousOn_all hv.continuous hr
  have hY0 : 0 ≤ c * sourceSup v r ^ β := by positivity
  have hZ0 : 0 ≤ c * sourceSup v r ^ (1 + α) := by positivity
  have hB : 0 ≤ 2 * sourceSup v r + c * d ^ α * sourceSup v r ^ (1 + α) +
      3 * c * d ^ β * sourceSup v r ^ (1 + β) := by positivity
  simp only [localTwoPointSup, iSup_le_iff]
  intro x hx y hy hxy
  apply ENNReal.ofReal_le_ofReal
  have hYi := (abs_sub_le_of_parabolicHolderSeminorm_le hY0 hY
    (mixedInterior_subset_positive hr hd.le hx) (mixedInterior_subset_positive hr hd.le hy)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Local.pdist_nonneg x y) hxy hβ) hY0)
  have hZi := (abs_sub_le_of_parabolicHolderSeminorm_le hZ0 hZ
    (mixedInterior_subset_positive hr hd.le hx) (mixedInterior_subset_positive hr hd.le hy)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Local.pdist_nonneg x y) hxy hα) hZ0)
  have hi := expansion_abs_le_of_increments v Y Z x y
    (abs_le_sourceSup_of_continuousOn hv.continuous hr (mixedInterior_subset_base hd.le hx))
    (abs_le_sourceSup_of_continuousOn hv.continuous hr (mixedInterior_subset_base hd.le hy)) hYi hZi
  have hp : sourceSup v r ^ (1 + β) = sourceSup v r * sourceSup v r ^ β := by
    rw [Real.rpow_add' hM (by linarith : 1 + β ≠ 0), Real.rpow_one]
  rw [hp]
  nlinarith only [hi]


theorem source_expansion_parent_two_point_reciprocal_positive {v Y Z : ParabolicSpace → ℝ}
    (hv : SourceCubicRegularity v) {r d α β c : ℝ}
    (hr : 0 ≤ r) (hd : 0 < d) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hM : 0 < sourceSup v r)
    (hscale : d * sourceSup v r ≤ 1)
    (hY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * sourceSup v r ^ β))
    (hZ : parabolicHolderSeminorm α (parabolicClosedNbhd mwCylinder 1) Z ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 + α))) :
    localTwoPointSup (fun p => Local.expansion v Y Z p.1 p.2)
      (Local.cylinderInterior r d) d ≤ ENNReal.ofReal (6 * sourceSup v r) := by
  apply (source_expansion_parent_two_point_positive hv hr hd hα hβ hc hY hZ).trans
  apply ENNReal.ofReal_le_ofReal
  have ha := parent_tree_weight hd hM hc hc1 hα hscale
  have hb := parent_tree_weight hd hM hc hc1 hβ hscale
  linarith


theorem source_radiusSourceUSup_parent_bound_positive {v Y Z : ParabolicSpace → ℝ}
    (hv : SourceCubicRegularity v) {r d₀ α β c : ℝ}
    (hr : 0 ≤ r) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hM : 0 < sourceSup v r)
    (hscale : d₀ * sourceSup v r ≤ 1)
    (hY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * sourceSup v r ^ β))
    (hZ : parabolicHolderSeminorm α (parabolicClosedNbhd mwCylinder 1) Z ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 + α))) :
    Local.radiusSourceUSup (sourceExpansion v Y Z) r d₀ ≤ ENNReal.ofReal (6 * sourceSup v r) := by
  simp only [Local.radiusSourceUSup, iSup_le_iff]
  intro d hd
  exact source_expansion_parent_two_point_reciprocal_positive hv hr hd.1 hα hβ hc hc1 hM
    ((mul_le_mul_of_nonneg_right hd.2 hM.le).trans hscale) hY hZ


end GlobalPhi43.MW20
