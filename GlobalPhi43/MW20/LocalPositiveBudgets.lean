module

public import GlobalPhi43.MW20.LocalPositiveCoefficient
public import GlobalPhi43.MW20.OnePointMajorantWeight
public import GlobalPhi43.MW20.SourceOnePointCoefficient
public import GlobalPhi43.MW20.ParentHolderNorm
public import GlobalPhi43.MW20.ParentExpansionIncrement
public import GlobalPhi43.MW20.RadiusAffineSeminorm
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.LocalSourceHolder
public import Mathlib.Basic.ENNReal.Real
public import GlobalPhi43.MW20.SourceConeEstimate
public import GlobalPhi43.MW20.RadiusCoefficientSup
public import GlobalPhi43.MW20.CylinderCoefficientBounds
public import GlobalPhi43.MW20.SourceAffineCoefficient
public import GlobalPhi43.Local.SchauderInputs
public import GlobalPhi43.MW20.ScalarHolderSeminorm
public import GlobalPhi43.MW20.ParentInterpolationAlgebra
public import GlobalPhi43.MW20.ParentHolderCutoff
public import GlobalPhi43.MW20.QuarterWeightTransfer
public import GlobalPhi43.MW20.SourceAffineFiniteness
public import GlobalPhi43.MW20.SourceHolderBridges
public import GlobalPhi43.MW20.SourceQuarterCoefficient
public import GlobalPhi43.MW20.ParentCoefficientAlgebra
public import GlobalPhi43.MW20.ParentCoefficientWeight
public import GlobalPhi43.MW20.CoefficientNormBridges
public import GlobalPhi43.MW20.ScalarSupNorm
public import GlobalPhi43.MW20.SourceWeightedAffineFiniteness
public import GlobalPhi43.MW20.SourceOnePointUniformBudget
public import GlobalPhi43.MW20.LocalHolderFiniteness
public import GlobalPhi43.MW20.ReciprocalScaleMonomial
public import GlobalPhi43.MW20.SourceRadiusWeightedFiniteness

/-! Localized parent-amplitude bounds in terms of local positive-tree norms. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem sourceOnePointCoefficient_parent_weight_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d ε c : ℝ} (L : ℝ) (hL : 0 ≤ L) (hLd : L ≤ d) (hr : 0 ≤ r) (hr1 : r < 1 / 2) (hd : 0 < d)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hMpos : 0 < sourceSup v r) (hscale : d * sourceSup v r ≤ 1) :
    let D := Local.cylinderInterior r d
    let Q := Local.cylinderInterior r (d / 4)
    let M := sourceSup v r
    let γ := (3 / 2 : ℝ) - 5 * ε
    let HU := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ d).toReal
    let Hq := (radiusAffineSeminorm (sourceExpansion v Y Z) Q γ (d / 4)).toReal
    let Cγ : ℝ := 200 * (2 ^ γ + 4) * (1 + 2 ^ γ)
    d ^ γ * sourceOnePointCoefficient v Y Z ε r d L c ≤
      smallScaleForcingConstant ε *
        (M + c * (d ^ γ * HU + (1325 + 4 ^ γ * (5 * Cγ)) * (d ^ γ * Hq + M))) := by
  have hs := source_parent_common_scalar_weighted_positive v Y Z hv hY hZ d hr hr1 hd
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscale
  have hn := source_parent_common_coefficient_sup_positive v Y Z hv hY hZ hr hr1 hd
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscale
  have hν := source_parent_common_coefficient_holder_positive v Y Z hv hY hZ hr hr1 hd
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscale
  have hD := mixedInterior_subset_unit_closedBall hr hd.le
  have hH := localSourceHolder_nonneg (localSourceHolder_bddAbove_of_smooth
    (fun a => v a + Z a) (hv.add hZ) _ 1 hD
    (by linarith : 0 ≤ 1 - 2 * ε) (by linarith : 1 - 2 * ε ≤ 1) d)
  have hHv := localSourceHolder_nonneg (localSourceHolder_bddAbove_of_smooth v hv _ 1 hD
    (by linarith : 0 ≤ 1 / 2 - 3 * ε) (by linarith : 1 / 2 - 3 * ε ≤ 1) d)
  have hw := sourceOnePointMajorant_weight_of_le
    (HU := (radiusAffineSeminorm (sourceExpansion v Y Z) (Local.cylinderInterior r d)
      ((3 / 2 : ℝ) - 5 * ε) d).toReal)
    (Hν := (localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z)
      (Local.cylinderInterior r d) (1 / 2 - 5 * ε)).toReal)
    (N := (localScalarSup (fun x => ‖sourceAffineCoefficient v Y Z x‖)
      (Local.cylinderInterior r d)).toReal) hL hLd hd hMpos hε.le hsmall
    hH hHv ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg hc hscale
  have hB : sourceSup v r ≤ d ^ ((3 / 2 : ℝ) - 5 * ε) *
      (radiusAffineSeminorm (sourceExpansion v Y Z) (Local.cylinderInterior r (d / 4))
        ((3 / 2 : ℝ) - 5 * ε) (d / 4)).toReal + sourceSup v r := by
    exact le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hd.le _) ENNReal.toReal_nonneg)
  dsimp only at hs hn hν hw ⊢
  unfold sourceOnePointCoefficient
  rw [← mul_assoc, mul_comm (d ^ _) (smallScaleForcingConstant ε), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (smallScaleForcingConstant_nonneg hsmall)
  apply hw.trans
  nlinarith only [mul_le_mul_of_nonneg_left hs.1 hc,
    mul_le_mul_of_nonneg_left hs.2 hc, mul_le_mul_of_nonneg_left hn hc,
    mul_le_mul_of_nonneg_left hν.2 hc, mul_le_mul_of_nonneg_left hB hc]


theorem sourceOnePointCoefficient_weighted_radius_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d d₀ ε c : ℝ} (L : ℝ) (hL : 0 ≤ L) (hLd : L ≤ d) (hr : 0 ≤ r) (hr1 : r < 1 / 2) (hd : 0 < d) (hdd : d ≤ d₀)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hMpos : 0 < sourceSup v r) (hscale : d * sourceSup v r ≤ 1) :
    let M := sourceSup v r
    let γ := (3 / 2 : ℝ) - 5 * ε
    let S := (Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ).toReal
    let Cγ : ℝ := 200 * (2 ^ γ + 4) * (1 + 2 ^ γ)
    let Kε : ℝ := 1 + (1325 + 4 ^ γ * (5 * Cγ)) * (4 ^ γ + 1)
    d ^ γ * sourceOnePointCoefficient v Y Z ε r d L c ≤
      smallScaleForcingConstant ε * (M + c * Kε * (S + M)) := by
  have hγ : 0 ≤ (3 / 2 : ℝ) - 5 * ε := by linarith
  have hγ2 : (3 / 2 : ℝ) - 5 * ε ≤ 2 := by linarith
  have hh := sourceOnePointCoefficient_parent_weight_positive v Y Z hv hY hZ L hL hLd
    hr hr1 hd hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscale
  have hs := source_weightedRadiusAffineSeminorm_scale_bound v Y Z hv hY hZ hr hγ hγ2 ⟨hd, hdd⟩
  have hq := source_weightedRadiusAffineSeminorm_quarter_bound v Y Z hv hY hZ hr hγ hγ2 ⟨hd, hdd⟩
  dsimp only at hh ⊢
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (smallScaleForcingConstant_nonneg hsmall)
  let S := (Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ ((3 / 2 : ℝ) - 5 * ε)).toReal
  let A : ℝ := 4 ^ ((3 / 2 : ℝ) - 5 * ε)
  let K : ℝ := 1325 + A * (5 * (200 * (2 ^ ((3 / 2 : ℝ) - 5 * ε) + 4) *
    (1 + 2 ^ ((3 / 2 : ℝ) - 5 * ε))))
  have hK : 0 ≤ K := by dsimp [K, A]; positivity
  have hS : 0 ≤ S := ENNReal.toReal_nonneg
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb := add_le_add hs (mul_le_mul_of_nonneg_left
    (add_le_add hq (le_refl (sourceSup v r))) hK)
  have he : S + K * (A * S + sourceSup v r) ≤
      (1 + K * (A + 1)) * (S + sourceSup v r) := by
    nlinarith only [mul_nonneg hK hS, mul_nonneg hK (mul_nonneg hA hMpos.le), hMpos.le]
  have hout := add_le_add (le_refl (sourceSup v r))
    (mul_le_mul_of_nonneg_left (hb.trans he) hc)
  dsimp [K, A, S] at hout
  nlinarith only [hout]


theorem sourceOnePointCoefficient_inner_weighted_radius_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d d₀ L ε c : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2) (hd : 0 < d) (hdd : d ≤ d₀)
    (hL : 0 ≤ L) (hLd : L ≤ d / 8)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hMpos : 0 < sourceSup v r) (hscale : d * sourceSup v r ≤ 1) :
    let γ := (3 / 2 : ℝ) - 5 * ε
    d ^ γ * sourceOnePointCoefficient v Y Z ε r (d / 4) L c ≤
      (4 : ℝ) ^ γ * sourceOnePointUniformBudget ε (sourceSup v r)
        (Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ).toReal c := by
  have hD : Local.cylinderInterior r d ⊆ Local.cylinderInterior r (d / 4) :=
    Local.cylinderInterior_mono (by positivity) (by linarith)
  have hh := sourceOnePointCoefficient_weighted_radius_positive v Y Z hv hY hZ L hL
    (by linarith : L ≤ d / 4) hr hr1 (by positivity : 0 < d / 4) (by linarith : d / 4 ≤ d₀) hε hsmall hc hc1
    (hne.mono hD) hbudgetY hbudgetZ hMpos (by nlinarith : d / 4 * sourceSup v r ≤ 1)
  change (d / 4) ^ ((3 / 2 : ℝ) - 5 * ε) * sourceOnePointCoefficient v Y Z ε r (d / 4) L c ≤
    sourceOnePointUniformBudget ε (sourceSup v r)
      (Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ ((3 / 2 : ℝ) - 5 * ε)).toReal c at hh
  have he : d ^ ((3 / 2 : ℝ) - 5 * ε) =
      (4 : ℝ) ^ ((3 / 2 : ℝ) - 5 * ε) * (d / 4) ^ ((3 / 2 : ℝ) - 5 * ε) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : 0 ≤ d / 4)]
    congr 1
    ring
  dsimp only
  rw [he, mul_assoc]
  exact mul_le_mul_of_nonneg_left hh (by positivity)


theorem source_three_point_parent_weight_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d ε c : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2) (hd : 0 < d)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hMpos : 0 < sourceSup v r) (hscale : d * sourceSup v r ≤ 1) :
    let D := Local.cylinderInterior r (d / 4)
    let M := sourceSup v r
    let α := (1 / 2 : ℝ) - 3 * ε
    let β := 1 - 2 * ε
    let γ := (3 / 2 : ℝ) - 5 * ε
    let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ (d / 4)).toReal
    d ^ γ * (3 * c * localSourceHolder v α D (d / 2) * M ^ β) ≤
      936 * c * (d ^ γ * H + M) := by
  have hh := source_parent_quarter_weighted_positive v Y Z hv hY hZ hr hr1 hd
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscale
  have hD := mixedInterior_subset_unit_closedBall hr (by positivity : 0 ≤ d / 4)
  have hHv := localSourceHolder_nonneg (localSourceHolder_bddAbove_of_smooth v hv _ 1 hD
    (by linarith : 0 ≤ (1 / 2 : ℝ) - 3 * ε)
    (by linarith : (1 / 2 : ℝ) - 3 * ε ≤ 1) (d / 2))
  have hw := reciprocal_scale_norm_monomial (γ := (3 / 2 : ℝ) - 5 * ε)
    (l := 0) (a := (1 / 2 : ℝ) - 3 * ε) (p := 1 - 2 * ε)
    hd hMpos (by linarith) hHv hscale (by ring)
  simp only [Real.rpow_zero, one_mul] at hw
  dsimp only at hh ⊢
  nlinarith only [mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 3 * c),
    mul_le_mul_of_nonneg_left hh.2.2 (by positivity : 0 ≤ 3 * c)]


theorem source_three_point_weighted_radius_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d d₀ ε c : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2) (hd : 0 < d) (hdd : d ≤ d₀)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hMpos : 0 < sourceSup v r) (hscale : d * sourceSup v r ≤ 1) :
    let D := Local.cylinderInterior r (d / 4)
    let M := sourceSup v r
    let α := (1 / 2 : ℝ) - 3 * ε
    let β := 1 - 2 * ε
    let γ := (3 / 2 : ℝ) - 5 * ε
    let S := (Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ).toReal
    d ^ γ * (3 * c * localSourceHolder v α D (d / 2) * M ^ β) ≤
      936 * c * (4 ^ γ + 1) * (S + M) := by
  have hh := source_three_point_parent_weight_positive v Y Z hv hY hZ hr hr1 hd
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscale
  have hq := source_weightedRadiusAffineSeminorm_quarter_bound v Y Z hv hY hZ hr
    (by linarith : 0 ≤ (3 / 2 : ℝ) - 5 * ε)
    (by linarith : (3 / 2 : ℝ) - 5 * ε ≤ 2) ⟨hd, hdd⟩
  dsimp only at hh ⊢
  apply hh.trans
  have hS : 0 ≤ (Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ ((3 / 2 : ℝ) - 5 * ε)).toReal :=
    ENNReal.toReal_nonneg
  have hA : 0 ≤ (4 : ℝ) ^ ((3 / 2 : ℝ) - 5 * ε) := by positivity
  have hm := mul_nonneg hA hMpos.le
  have hb := mul_le_mul_of_nonneg_left
    (add_le_add hq (le_refl (sourceSup v r))) (by positivity : 0 ≤ 936 * c)
  nlinarith only [hb, mul_nonneg (by positivity : 0 ≤ 936 * c) (add_nonneg hm hS)]


end GlobalPhi43.MW20
