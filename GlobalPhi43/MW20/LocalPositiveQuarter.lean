module

public import GlobalPhi43.MW20.LocalPositiveRadiusRows
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

/-! Localized parent-amplitude estimates in terms of local positive-tree norms,
with the norms taken on the specified local domains. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem source_parent_quarter_all_cutoffs_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d ε c : ℝ} (L : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 2) (hd : 0 < d)
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
    d * sSup ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' D) ≤
      72 * (d ^ γ * H + M) ∧
    d ^ β * localSourceHolder (fun x => v x + Z x) β D L ≤
      312 * (d ^ γ * H + M) ∧
    d ^ α * localSourceHolder v α D L ≤ 312 * (d ^ γ * H + M) := by
  have hfinite := source_expansion_radiusAffine_ne_top v Y Z hv hY hZ hr
    (by positivity : 0 ≤ d / 4) (by linarith : 0 ≤ (3 / 2 : ℝ) - 5 * ε)
    (by linarith : (3 / 2 : ℝ) - 5 * ε ≤ 2) (d / 4)
  let D := Local.cylinderInterior r (d / 4)
  let M := sourceSup v r
  let α := (1 / 2 : ℝ) - 3 * ε
  let β := 1 - 2 * ε
  let γ := (3 / 2 : ℝ) - 5 * ε
  let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ (d / 4)).toReal
  let N := sSup ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' D)
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hβ1 : β ≤ 1 := by dsimp [β]; linarith
  have hαβ : α ≤ β := by dsimp [α, β]; linarith
  have hγ : 1 < α + β := by dsimp [α, β]; linarith
  have heγ : α + β = γ := by dsimp [α, β, γ]; ring
  have hd1 : d < 1 := by obtain ⟨x, hx⟩ := hne; exact mixedInterior_depth_lt_one hr hx
  have hD : Local.cylinderInterior r d ⊆ D :=
    Local.cylinderInterior_mono (by positivity) (by linarith)
  have hneQ : D.Nonempty := hne.mono hD
  have hq : 0 < d / 4 := by positivity
  have hcone : d / 4 ≤ 1 / 2 - d / 4 := by linarith
  have hfinite' : radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) (d / 4) ≠ ⊤ := by
    simpa only [heγ] using hfinite
  have hM : 0 ≤ M := hMpos.le
  have hscaleQ : d / 4 * M ≤ 1 := by dsimp only [M]; nlinarith
  have hh := source_parent_radius_weighted_all_cutoffs_positive (L := L) v Y Z hv hY hZ
    hr hr1 hq hcone hα hβ hαβ hβ1 hγ hc hc1 hneQ hfinite' hbudgetY hbudgetZ hMpos hscaleQ
  simp only [heγ] at hh
  have hcN := source_parent_radius_coefficient_row_positive v Y Z hv hY hZ hr hr1 hq hcone
    hα hβ hγ hc hneQ hfinite' hbudgetY hbudgetZ
  have hN : 0 ≤ N := by
    obtain ⟨x, hx⟩ := hneQ
    exact (norm_nonneg _).trans (le_csSup hcN.1 ⟨x, hx, rfl⟩)
  have hDb : D ⊆ Metric.closedBall 0 1 :=
    mixedInterior_subset_unit_closedBall hr hq.le
  have hbV := localSourceHolder_bddAbove_of_smooth v hv D 1 hDb hα
    (hαβ.trans hβ1) L
  have hbS := localSourceHolder_bddAbove_of_smooth (fun x => v x + Z x)
    (hv.add hZ) D 1 hDb hβ hβ1 L
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hγ0 : 0 ≤ γ := by rw [← heγ]; linarith
  have hNw := quarter_weight_transfer hd (le_refl 1) hγ0 hN hH
    (by norm_num : (0 : ℝ) ≤ 18) (by simpa only [Real.rpow_one] using hh.1)
  have hSw := quarter_weight_transfer hd hβ1 hγ0 (localSourceHolder_nonneg hbS) hH
    (by norm_num : (0 : ℝ) ≤ 78) hh.2.1
  have hVw := quarter_weight_transfer hd (hαβ.trans hβ1) hγ0 (localSourceHolder_nonneg hbV) hH
    (by norm_num : (0 : ℝ) ≤ 78) hh.2.2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Real.rpow_one, show (4 : ℝ) * 18 = 72 by norm_num] using hNw
  · simpa only [show (4 : ℝ) * 78 = 312 by norm_num] using hSw
  · simpa only [show (4 : ℝ) * 78 = 312 by norm_num] using hVw


theorem source_parent_quarter_weighted_positive
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
    d * sSup ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' D) ≤
      72 * (d ^ γ * H + M) ∧
    d ^ β * localSourceHolder (fun x => v x + Z x) β D (d / 2) ≤
      312 * (d ^ γ * H + M) ∧
    d ^ α * localSourceHolder v α D (d / 2) ≤ 312 * (d ^ γ * H + M) := by
  exact source_parent_quarter_all_cutoffs_positive v Y Z hv hY hZ (d / 2)
    hr hr1 hd hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscale


theorem source_parent_common_scalar_weighted_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d ε c : ℝ} (L : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 2) (hd : 0 < d)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hMpos : 0 < sourceSup v r) (hscale : d * sourceSup v r ≤ 1) :
    let Q := Local.cylinderInterior r (d / 4)
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let α := (1 / 2 : ℝ) - 3 * ε
    let β := 1 - 2 * ε
    let γ := (3 / 2 : ℝ) - 5 * ε
    let H := (radiusAffineSeminorm (sourceExpansion v Y Z) Q γ (d / 4)).toReal
    d ^ β * localSourceHolder (fun x => v x + Z x) β D L ≤
      312 * (d ^ γ * H + M) ∧
    d ^ α * localSourceHolder v α D L ≤ 312 * (d ^ γ * H + M) := by
  have hh := source_parent_quarter_all_cutoffs_positive v Y Z hv hY hZ L hr hr1 hd
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscale
  have hD : Local.cylinderInterior r d ⊆ Local.cylinderInterior r (d / 4) :=
    Local.cylinderInterior_mono (by positivity) (by linarith)
  have hDb := mixedInterior_subset_unit_closedBall hr (by positivity : 0 ≤ d / 4)
  have hbV := localSourceHolder_bddAbove_of_smooth v hv _ 1 hDb
    (by linarith : 0 ≤ (1 / 2 : ℝ) - 3 * ε)
    (by linarith : (1 / 2 : ℝ) - 3 * ε ≤ 1) L
  have hbS := localSourceHolder_bddAbove_of_smooth (fun x => v x + Z x)
    (hv.add hZ) _ 1 hDb (by linarith : 0 ≤ 1 - 2 * ε)
    (by linarith : 1 - 2 * ε ≤ 1) L
  exact ⟨(mul_le_mul_of_nonneg_left
    (localSourceHolder_mono_of_bddAbove _ _ hD le_rfl hbS)
    (Real.rpow_nonneg hd.le _)).trans hh.2.1,
    (mul_le_mul_of_nonneg_left
    (localSourceHolder_mono_of_bddAbove _ _ hD le_rfl hbV)
    (Real.rpow_nonneg hd.le _)).trans hh.2.2⟩


end GlobalPhi43.MW20
