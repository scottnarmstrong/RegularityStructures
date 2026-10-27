module

public import GlobalPhi43.MW20.LocalPositiveCoefficient

public import GlobalPhi43.MW20.FullAffineFromRadiusFar
public import GlobalPhi43.MW20.ClosingFarAffine
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
public import GlobalPhi43.MW20.LocalHolderFiniteness
public import GlobalPhi43.MW20.ScalarSupNorm
public import GlobalPhi43.MW20.SourceRadiusWeightedFiniteness

/-! The full source affine norm, with far pairs explicitly paid. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- In the actual source expansion, a prior radius bound controls the full
norm only after parent-amplitude and coefficient estimates pay every far
pair. This is not an unrestricted radius-to-full embedding for arbitrary U. -/
theorem source_full_affine_from_radius_bound_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d₀ d ε c A : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : d ∈ Ioc (0 : ℝ) d₀) (hε : 0 < ε) (hsmall : ε < 1 / 14)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hA : 0 ≤ A)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hMpos : 0 < sourceSup v r) (hscale : d₀ * sourceSup v r ≤ 1)
    (hnorm : Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ ((3 / 2 : ℝ) - 5 * ε) ≤
      ENNReal.ofReal (A * sourceSup v r)) :
    let γ := (3 / 2 : ℝ) - 5 * ε
    ENNReal.ofReal (d ^ γ) * localAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) γ ≤
        ENNReal.ofReal ((A + 6 + 216 * (4 ^ γ * A + 1)) * sourceSup v r) := by
  let U := sourceExpansion v Y Z
  let D := Local.cylinderInterior r d
  let γ := (3 / 2 : ℝ) - 5 * ε
  let M := sourceSup v r
  let ν := sourceAffineCoefficient v Y Z
  let N := (localScalarSup (fun x => ‖ν x‖) D).toReal
  let CN := 72 * ((4 : ℝ) ^ γ * A + 1)
  have hdpos := hd.1
  have hγ : 1 < γ := by dsimp [γ]; linarith
  have hγ2 : γ ≤ 2 := by dsimp [γ]; linarith
  have hdpow : 0 < d ^ γ := Real.rpow_pos_of_pos hd.1 γ
  have hCN : 0 ≤ CN := by dsimp [CN]; positivity
  have hS := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  rw [ENNReal.toReal_ofReal (mul_nonneg hA hMpos.le)] at hS
  have hscaleD : d * sourceSup v r ≤ 1 :=
    (mul_le_mul_of_nonneg_right hd.2 hMpos.le).trans hscale
  have hq := (source_weightedRadiusAffineSeminorm_quarter_bound v Y Z hv hY hZ hr
    (by linarith : 0 ≤ γ) hγ2 hd).trans (mul_le_mul_of_nonneg_left hS (by positivity))
  have hNb := source_parent_common_coefficient_sup_positive v Y Z hv hY hZ hr hr1 hd.1
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscaleD
  have hNw : d * N ≤ CN * M := by
    dsimp only [CN, N, D, ν, M] at hNb ⊢
    nlinarith only [hNb, hq]
  have hνc := (sourceAffineCoefficient_contDiff v Y Z hv hY hZ).continuous
  have hNfinite := localScalarSup_ne_top (fun x => ‖ν x‖) hνc.norm D
    (Metric.closedBall 0 1) (mixedInterior_subset_unit_closedBall hr hd.1.le) (isCompact_closedBall _ _)
  have hNpoint (x : ParabolicSpace) (hx : x ∈ D) : ‖ν x‖ ≤ N := by
    have hn : localScalarSup (fun x => ‖ν x‖) D ≤ ENNReal.ofReal N := by
      rw [ENNReal.ofReal_toReal hNfinite]
    simpa only [abs_of_nonneg (norm_nonneg _)] using
      localScalarSup_bound (fun x => ‖ν x‖) D ENNReal.toReal_nonneg hn hx
  have hradReal := (source_weightedRadiusAffineSeminorm_scale_bound v Y Z hv hY hZ hr
    (by linarith : 0 ≤ γ) hγ2 hd).trans hS
  have hradFinite := source_expansion_radiusAffine_ne_top v Y Z hv hY hZ hr hd.1.le
    (by linarith : 0 ≤ γ) hγ2 d
  have hrad : radiusAffineSeminorm U D γ d ≤ ENNReal.ofReal (A * M / d ^ γ) := by
    rw [← ENNReal.ofReal_toReal hradFinite]
    apply ENNReal.ofReal_le_ofReal
    exact (le_div_iff₀ hdpow).2 (by nlinarith only [hradReal])
  have hfar : ∀ x ∈ D, ∀ y ∈ D, d < Local.pdist x y →
      |U (x, y) - ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i)| ≤
        ((6 + 3 * CN) * M / d ^ γ) * Local.pdist x y ^ γ := by
    intro x hx y hy hxy
    have hw := source_far_affine_remainder_positive v Y Z
      (sourceCubicRegularity_of_contDiff (hv.of_le (by simp))) hr hd.1
      (by linarith : 0 ≤ (1 / 2 : ℝ) - 3 * ε) (by linarith : 0 ≤ 1 - 2 * ε)
      (by dsimp [γ]; linarith : (1 / 2 : ℝ) - 3 * ε ≤ γ)
      (by dsimp [γ]; linarith : 1 - 2 * ε ≤ γ) hγ.le hc hc1 hbudgetY hbudgetZ
      hMpos hscaleD hx hy hxy.le (hNpoint x hx)
    change (d ^ γ / Local.pdist x y ^ γ) *
      |U (x, y) - ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i)| ≤
      6 * M + 3 * d * N at hw
    have hw' : (d ^ γ / Local.pdist x y ^ γ) *
        |U (x, y) - ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i)| ≤ (6 + 3 * CN) * M := by
      nlinarith only [hw, hNw]
    have hppow : 0 < Local.pdist x y ^ γ := Real.rpow_pos_of_pos (hd.1.trans hxy) γ
    have hm := mul_le_mul_of_nonneg_right hw' hppow.le
    have he : (d ^ γ / Local.pdist x y ^ γ) *
        |U (x, y) - ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i)| * Local.pdist x y ^ γ =
        d ^ γ * |U (x, y) - ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i)| := by
      field_simp
    rw [he] at hm
    apply le_of_mul_le_mul_left (hm.trans_eq ?_) hdpow
    field_simp
  have hf := localAffineSeminorm_le_radius_and_far U (sourceExpansion_contDiff v Y Z hv hY hZ)
    D (isOpen_cylinderInterior r d) hγ hd.1 (by positivity) (by positivity) hrad hfar
  dsimp only
  calc
    _ ≤ ENNReal.ofReal (d ^ γ) * ENNReal.ofReal (A * M / d ^ γ + (6 + 3 * CN) * M / d ^ γ) :=
      mul_le_mul' le_rfl hf
    _ = ENNReal.ofReal (d ^ γ * (A * M / d ^ γ + (6 + 3 * CN) * M / d ^ γ)) := by
      rw [ENNReal.ofReal_mul hdpow.le]
    _ = _ := by
      congr 1
      dsimp only [CN, M, γ]
      field_simp
      ring

end GlobalPhi43.MW20
