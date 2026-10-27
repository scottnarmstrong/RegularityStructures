module

public import GlobalPhi43.MW20.LocalPositiveBudgets
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.LocalSourceHolder
public import Mathlib.Basic.ENNReal.Real
public import GlobalPhi43.MW20.SourceConeEstimate
public import GlobalPhi43.MW20.ParentHolderNorm
public import GlobalPhi43.MW20.ParentExpansionIncrement
public import GlobalPhi43.MW20.RadiusAffineSeminorm
public import GlobalPhi43.MW20.RadiusCoefficientSup
public import GlobalPhi43.MW20.CylinderCoefficientBounds
public import GlobalPhi43.MW20.SourceAffineCoefficient
public import GlobalPhi43.Local.SchauderInputs
public import GlobalPhi43.MW20.ScalarHolderSeminorm
public import GlobalPhi43.MW20.ParentInterpolationAlgebra
public import GlobalPhi43.MW20.ParentHolderCutoff
public import GlobalPhi43.MW20.QuarterWeightTransfer
public import GlobalPhi43.MW20.SourceAffineFiniteness
public import GlobalPhi43.MW20.LocalHolderFiniteness
public import GlobalPhi43.MW20.ReciprocalScaleMonomial
public import GlobalPhi43.MW20.SourceRadiusWeightedFiniteness
public import GlobalPhi43.MW20.SourceSchauderExponents
public import GlobalPhi43.Local.TimeFreeGeometry

/-! Full all-time rectangular three-point bound from local positive-tree norms. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem source_three_point_all_time_orders_positive
    (v Y Z : ParabolicSpace → ℝ) (hv : SourceCubicRegularity v)
    {r d L₁ L₂ α β c : ℝ} (hr : 0 ≤ r) (hd : 0 < d) (hL₁ : L₁ ≤ d / 2)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hbudgetY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * sourceSup v r ^ β))
    {x y z : ParabolicSpace} (hzpos : z ∈ parabolicClosedNbhd mwCylinder 1) (hx : x ∈ Local.cylinderInterior r d)
    (hy : y ∈ Local.cylinderInterior r (d / 4))
    (hxy : Local.pdist x y ≤ L₁) (hyz : Local.pdist y z ≤ L₂) :
    |Local.expansion v Y Z x z - Local.expansion v Y Z x y - Local.expansion v Y Z y z| ≤
      (3 * c * localSourceHolder v α (Local.cylinderInterior r (d / 4)) (d / 2) *
        sourceSup v r ^ β) * L₁ ^ α * L₂ ^ β := by
  have hxQ := Local.cylinderInterior_mono (by positivity : 0 ≤ d / 4)
    (by linarith : d / 4 ≤ d) hx
  have hL : d / 2 ≤ 1 := by linarith [mixedInterior_depth_lt_one hr hx]
  have hb := mixedInteriorHolder_bddAbove hv hr (by positivity : 0 < d / 4) hα1 hL
  have hH := localSourceHolder_nonneg hb
  have hM := sourceSup_nonneg_of_continuousOn_all hv.continuous hr
  have hvxy := (localSourceHolder_increment hb hxQ hy (hxy.trans hL₁) hL).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Local.pdist_nonneg x y) hxy hα) hH)
  have hyz' := (abs_sub_le_of_parabolicHolderSeminorm_le (show 0 ≤ c * sourceSup v r ^ β by positivity)
    hbudgetY (mixedInterior_subset_positive hr (by positivity : 0 ≤ d / 4) hy) hzpos).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Local.pdist_nonneg y z) hyz hβ)
      (show 0 ≤ c * sourceSup v r ^ β by positivity))
  have hp := mul_le_mul hvxy hyz' (abs_nonneg _) ((abs_nonneg _).trans hvxy)
  rw [Local.expansion_three_point]
  simp only [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  nlinarith only [hp]


theorem source_three_point_weighted_radius_input_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d d₀ ε c : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2) (hd : 0 < d) (hdd : d ≤ d₀)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hMpos : 0 < sourceSup v r) (hscale : d * sourceSup v r ≤ 1)
    {x y z : ParabolicSpace} (hx : x ∈ Local.cylinderInterior r d)
    (hyD : y ∈ sourceCylinder r) (hy : y ∈ Local.symmetricBall x (d / 2))
    (hzD : z ∈ sourceCylinder r) (hz : z ∈ Local.symmetricBall y (d / 4)) :
    let γ := (3 / 2 : ℝ) - 5 * ε
    let S := (Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ).toReal
    d ^ γ * |Local.expansion v Y Z x z - Local.expansion v Y Z x y - Local.expansion v Y Z y z| ≤
      (936 * c * (4 ^ γ + 1) * (S + sourceSup v r)) *
        (∑ a ∈ sourceSchauderExponents ε,
          Local.pdist x y ^ a * Local.pdist y z ^ (γ - a)) := by
  have hdom := Local.time_free_three_point_domain hd.le hx hyD hy hzD hz
  have hxy : Local.pdist x y ≤ d / 2 := hy.le
  have hn := source_three_point_all_time_orders_positive v Y Z (z := z) (L₂ := Local.pdist y z)
    (hzpos := sourceCylinder_subset_positive hr hzD)
    (sourceCubicRegularity_of_contDiff (hv.of_le (by simp))) hr hd hxy
    (by linarith : 0 ≤ (1 / 2 : ℝ) - 3 * ε)
    (by linarith : (1 / 2 : ℝ) - 3 * ε ≤ 1)
    (by linarith : 0 ≤ 1 - 2 * ε) hc hbudgetY hx hdom.2.1 le_rfl le_rfl
  have hb := source_three_point_weighted_radius_positive v Y Z hv hY hZ hr hr1 hd hdd
    hε hsmall hc hc1 ⟨x, hx⟩ hbudgetY hbudgetZ hMpos hscale
  have ht := Finset.single_le_sum
    (s := sourceSchauderExponents ε)
    (f := fun a => Local.pdist x y ^ a * Local.pdist y z ^ (((3 / 2 : ℝ) - 5 * ε) - a))
    (fun a _ => mul_nonneg (Real.rpow_nonneg (Local.pdist_nonneg _ _) _)
      (Real.rpow_nonneg (Local.pdist_nonneg _ _) _))
    (sourceSchauderExponents_three_point ε)
  have he : ((3 / 2 : ℝ) - 5 * ε) - (1 / 2 - 3 * ε) = 1 - 2 * ε := by ring
  rw [he] at ht
  have hK : 0 ≤ 936 * c * ((4 : ℝ) ^ ((3 / 2 : ℝ) - 5 * ε) + 1) *
      ((Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ ((3 / 2 : ℝ) - 5 * ε)).toReal + sourceSup v r) := by
    positivity
  dsimp only at hb ⊢
  have hstep := mul_le_mul_of_nonneg_left hn
    (Real.rpow_nonneg hd.le ((3 / 2 : ℝ) - 5 * ε))
  have hbound := mul_le_mul_of_nonneg_right hb
    (mul_nonneg (Real.rpow_nonneg (Local.pdist_nonneg x y) ((1 / 2 : ℝ) - 3 * ε))
      (Real.rpow_nonneg (Local.pdist_nonneg y z) (1 - 2 * ε)))
  have hsum := mul_le_mul_of_nonneg_left ht hK
  nlinarith only [hstep, hbound, hsum]


end GlobalPhi43.MW20
