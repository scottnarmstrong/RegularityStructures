module

public import GlobalPhi43.MW20.LocalPositiveQuarter
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.LocalSourceHolder
public import Mathlib.Basic.ENNReal.Real
public import GlobalPhi43.MW20.SourceConeEstimate
public import GlobalPhi43.MW20.SourceHolderBridges
public import GlobalPhi43.MW20.SourceQuarterCoefficient
public import GlobalPhi43.MW20.ParentCoefficientAlgebra
public import GlobalPhi43.MW20.ParentHolderNorm
public import GlobalPhi43.MW20.ParentExpansionIncrement
public import GlobalPhi43.MW20.RadiusAffineSeminorm
public import GlobalPhi43.MW20.RadiusCoefficientSup
public import GlobalPhi43.MW20.CylinderCoefficientBounds
public import GlobalPhi43.MW20.SourceAffineCoefficient
public import GlobalPhi43.Local.SchauderInputs
public import GlobalPhi43.MW20.ScalarHolderSeminorm
public import GlobalPhi43.MW20.ParentInterpolationAlgebra
public import GlobalPhi43.MW20.ParentCoefficientWeight
public import GlobalPhi43.MW20.QuarterWeightTransfer
public import GlobalPhi43.MW20.SourceAffineFiniteness
public import GlobalPhi43.MW20.CoefficientNormBridges
public import GlobalPhi43.MW20.ParentHolderCutoff
public import GlobalPhi43.MW20.LocalHolderFiniteness
public import GlobalPhi43.MW20.ScalarSupNorm

/-! Localized parent-amplitude estimates in terms of local positive-tree norms,
with the norms taken on the specified local domains. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem source_parent_coefficient_holder_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d ε c : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : 0 < d) (hcone : d / 2 ≤ 1 / 2 - d)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hfinite : radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) (3 / 2 - 5 * ε) d ≠ ⊤)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε)))) :
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let α := (1 / 2 : ℝ) - 3 * ε
    let β := 1 - 2 * ε
    let γ := (3 / 2 : ℝ) - 5 * ε
    let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ d).toReal
    localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε) ≤
      ENNReal.ofReal (2 * (2 ^ γ + 4) *
        (H + 3 * localSourceHolder v α D d * (c * M ^ β) +
          (d / 2) ^ (-γ) * (2 * M + c * d ^ α * M ^ (1 + α) +
            3 * c * d ^ β * M ^ (1 + β)))) := by
  let D := Local.cylinderInterior r d
  let M := sourceSup v r
  let α := (1 / 2 : ℝ) - 3 * ε
  let β := 1 - 2 * ε
  let γ := (3 / 2 : ℝ) - 5 * ε
  let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ d).toReal
  have hvreg := sourceCubicRegularity_of_contDiff (hv.of_le (by simp))
  have hM : 0 ≤ M := sourceSup_nonneg_of_continuousOn_all hvreg.continuous hr
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hd1 : d ≤ 1 := by obtain ⟨x, hx⟩ := hne; exact (mixedInterior_depth_lt_one hr hx).le
  have hb := mixedInteriorHolder_bddAbove hvreg hr hd
    (show α ≤ 1 by dsimp [α]; linarith) hd1
  have hV : 0 ≤ localSourceHolder v α D d := localSourceHolder_nonneg hb
  have hVnorm := (radiusHolderSeminorm_mono v (α := α)
    (show D ⊆ D from fun _ h => h) (show d / 2 ≤ d by linarith)).trans
      (radiusHolderSeminorm_le_localSourceHolder hb hd1)
  have hYnorm : radiusHolderSeminorm Y D β (d / 2) ≤ ENNReal.ofReal (c * M ^ β) :=
    (radiusHolderSeminorm_le_parabolicHolderSeminorm Y (mixedInterior_subset_positive hr hd.le) β (d / 2)).trans hbudgetY
  have hsup := (localTwoPointSup_mono_radius (sourceExpansion v Y Z) D
    (show d / 2 ≤ d by linarith)).trans
      (source_expansion_parent_two_point_positive hvreg hr hd hα hβ hc hbudgetY hbudgetZ)
  have hnorm : radiusAffineSeminorm (sourceExpansion v Y Z) D γ d ≤ ENNReal.ofReal H := by
    dsimp only [H]
    rw [ENNReal.ofReal_toReal hfinite]
  have hh := source_global_radius_coefficient_bounds v Y Z hv hY hZ hr1 hε hsmall hne
    (by positivity : 0 < d / 2) hcone (le_refl (d / 2)) ENNReal.toReal_nonneg
    (by positivity) hV (show 0 ≤ c * M ^ β by positivity) hnorm hsup hVnorm hYnorm
  simpa only [show -(3 / 2 : ℝ) + 5 * ε = -γ by dsimp [γ]; ring] using hh.2.2


theorem source_parent_coefficient_row_4_17_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d ε c : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : 0 < d) (hcone : d ≤ 1 / 2 - d)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hfinite : radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) (3 / 2 - 5 * ε) d ≠ ⊤)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hMpos : 0 < sourceSup v r) :
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let α := (1 / 2 : ℝ) - 3 * ε
    let β := 1 - 2 * ε
    let γ := (3 / 2 : ℝ) - 5 * ε
    let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ d).toReal
    localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε) ≤
      ENNReal.ofReal (200 * (2 ^ γ + 4) * (1 + 2 ^ γ) *
        ((1 + c * d ^ β * M ^ β) * H + c ^ 2 * M ^ (1 + γ) +
          c ^ 2 * d ^ (β - α) * M ^ (1 + 2 * β) + d ^ (-γ) * M +
          c * d ^ (-β) * M ^ (1 + α) + c * d ^ (-α) * M ^ (1 + β))) := by
  let D := Local.cylinderInterior r d
  let M := sourceSup v r
  let α := (1 / 2 : ℝ) - 3 * ε
  let β := 1 - 2 * ε
  let γ := (3 / 2 : ℝ) - 5 * ε
  let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ d).toReal
  let V := localSourceHolder v α D d
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hαβ : α ≤ β := by dsimp [α, β]; linarith
  have hβ1 : β ≤ 1 := by dsimp [β]; linarith
  have hγ : 1 < α + β := by dsimp [α, β]; linarith
  have heγ : α + β = γ := by dsimp [α, β, γ]; ring
  have hfinite' : radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) d ≠ ⊤ := by
    simpa only [heγ] using hfinite
  have hrows := source_parent_radius_interpolation_rows_positive v Y Z hv hY hZ hr hr1 hd hcone
    hα hβ hαβ hβ1 hγ hc hne hfinite' hbudgetY hbudgetZ
  have hV : V ≤ 24 * (d ^ β * H + d ^ (-α) * M + c * M ^ (1 + α) +
      c * d ^ (β - α) * M ^ (1 + β)) := by
    simpa only [heγ] using hrows.2.2
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hs := parent_coefficient_holder_substitution hd hMpos hc hH hV
  rw [heγ] at hs
  have hnorm := source_parent_coefficient_holder_positive v Y Z hv hY hZ hr hr1 hd
    (by linarith : d / 2 ≤ 1 / 2 - d) hε hsmall hc hne hfinite hbudgetY hbudgetZ
  apply hnorm.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (2 * (2 ^ γ + 4)) * (100 * (1 + 2 ^ γ) *
        ((1 + c * d ^ β * M ^ β) * H + c ^ 2 * M ^ (1 + γ) +
          c ^ 2 * d ^ (β - α) * M ^ (1 + 2 * β) + d ^ (-γ) * M +
          c * d ^ (-β) * M ^ (1 + α) + c * d ^ (-α) * M ^ (1 + β))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring


theorem source_parent_coefficient_weighted_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d ε c : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : 0 < d) (hcone : d ≤ 1 / 2 - d)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hfinite : radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) (3 / 2 - 5 * ε) d ≠ ⊤)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hMpos : 0 < sourceSup v r) (hscale : d * sourceSup v r ≤ 1) :
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let γ := (3 / 2 : ℝ) - 5 * ε
    let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ d).toReal
    let Q := localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε)
    let Cγ : ℝ := 200 * (2 ^ γ + 4) * (1 + 2 ^ γ)
    Q ≠ ⊤ ∧ d ^ γ * Q.toReal ≤ 5 * Cγ * (d ^ γ * H + M) := by
  let D := Local.cylinderInterior r d
  let M := sourceSup v r
  let a := (1 / 2 : ℝ) - 3 * ε
  let b := 1 - 2 * ε
  let γ := (3 / 2 : ℝ) - 5 * ε
  let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ d).toReal
  let Q := localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε)
  let Cγ : ℝ := 200 * (2 ^ γ + 4) * (1 + 2 ^ γ)
  let S := (1 + c * d ^ b * M ^ b) * H + c ^ 2 * M ^ (1 + γ) +
    c ^ 2 * d ^ (b - a) * M ^ (1 + 2 * b) + d ^ (-γ) * M +
    c * d ^ (-b) * M ^ (1 + a) + c * d ^ (-a) * M ^ (1 + b)
  have ha : 0 ≤ a := by dsimp only [a]; linarith
  have hb : 0 ≤ b := by dsimp only [b]; linarith
  have hγ : a + b = γ := by dsimp only [a, b, γ]; ring
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hM : 0 ≤ M := hMpos.le
  have hCγ : 0 ≤ Cγ := by dsimp only [Cγ]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hnorm := source_parent_coefficient_row_4_17_positive v Y Z hv hY hZ hr hr1 hd hcone
    hε hsmall hc hne hfinite hbudgetY hbudgetZ hMpos
  change Q ≤ ENNReal.ofReal (Cγ * S) at hnorm
  have hQfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnorm
  have hreal : Q.toReal ≤ Cγ * S := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    rwa [ENNReal.toReal_ofReal (mul_nonneg hCγ hS)] at hh
  have hweight := parent_coefficient_envelope_weight hd hMpos hc hc1 ha hb hH hscale
  rw [hγ] at hweight
  change d ^ γ * S ≤ 5 * (d ^ γ * H + M) at hweight
  refine ⟨hQfinite, ?_⟩
  calc
    d ^ γ * Q.toReal ≤ d ^ γ * (Cγ * S) :=
      mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg hd.le γ)
    _ = Cγ * (d ^ γ * S) := by ring
    _ ≤ Cγ * (5 * (d ^ γ * H + M)) := mul_le_mul_of_nonneg_left hweight hCγ
    _ = _ := by ring


theorem source_parent_quarter_coefficient_holder_positive
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
    let γ := (3 / 2 : ℝ) - 5 * ε
    let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ (d / 4)).toReal
    let Q := localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε)
    let Cγ : ℝ := 200 * (2 ^ γ + 4) * (1 + 2 ^ γ)
    Q ≠ ⊤ ∧ d ^ γ * Q.toReal ≤ (4 : ℝ) ^ γ * (5 * Cγ) * (d ^ γ * H + M) := by
  have hfinite := source_expansion_radiusAffine_ne_top v Y Z hv hY hZ hr
    (by positivity : 0 ≤ d / 4) (by linarith : 0 ≤ (3 / 2 : ℝ) - 5 * ε)
    (by linarith : (3 / 2 : ℝ) - 5 * ε ≤ 2) (d / 4)
  let D := Local.cylinderInterior r (d / 4)
  let M := sourceSup v r
  let γ := (3 / 2 : ℝ) - 5 * ε
  let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ (d / 4)).toReal
  let Q := localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε)
  let Cγ : ℝ := 200 * (2 ^ γ + 4) * (1 + 2 ^ γ)
  have hd1 : d < 1 := by obtain ⟨x, hx⟩ := hne; exact mixedInterior_depth_lt_one hr hx
  have hD : Local.cylinderInterior r d ⊆ D :=
    Local.cylinderInterior_mono (by positivity) (by linarith)
  have hneQ : D.Nonempty := hne.mono hD
  have hM : 0 ≤ M := hMpos.le
  have hscaleQ : d / 4 * M ≤ 1 := by dsimp only [M]; nlinarith
  have hinner := source_parent_coefficient_weighted_positive v Y Z hv hY hZ hr hr1
    (by positivity : 0 < d / 4) (by linarith : d / 4 ≤ 1 / 2 - d / 4)
    hε hsmall hc hc1 hneQ hfinite hbudgetY hbudgetZ hMpos hscaleQ
  change Q ≠ ⊤ ∧ (d / 4) ^ γ * Q.toReal ≤ 5 * Cγ * ((d / 4) ^ γ * H + M) at hinner
  refine ⟨hinner.1, ?_⟩
  exact quarter_weight_transfer_exact hd (by dsimp only [γ]; linarith : 0 ≤ γ)
    ENNReal.toReal_nonneg (by positivity) hinner.2


theorem source_parent_common_coefficient_holder_positive
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
    let D := Local.cylinderInterior r d
    let E := Local.cylinderInterior r (d / 4)
    let M := sourceSup v r
    let γ := (3 / 2 : ℝ) - 5 * ε
    let H := (radiusAffineSeminorm (sourceExpansion v Y Z) E γ (d / 4)).toReal
    let Q := localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε)
    let Cγ : ℝ := 200 * (2 ^ γ + 4) * (1 + 2 ^ γ)
    Q ≠ ⊤ ∧ d ^ γ * Q.toReal ≤ (4 : ℝ) ^ γ * (5 * Cγ) * (d ^ γ * H + M) := by
  have hh := source_parent_quarter_coefficient_holder_positive v Y Z hv hY hZ hr hr1 hd
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscale
  have hD : Local.cylinderInterior r d ⊆ Local.cylinderInterior r (d / 4) :=
    Local.cylinderInterior_mono (by positivity) (by linarith)
  have hm := localCoefficientHolderSeminorm_mono (sourceAffineCoefficient v Y Z)
    (1 / 2 - 5 * ε) hD
  exact ⟨ne_top_of_le_ne_top hh.1 hm,
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hh.1 hm)
      (Real.rpow_nonneg hd.le _)).trans hh.2⟩


theorem source_parent_common_coefficient_sup_positive
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
    let D := Local.cylinderInterior r d
    let Q := Local.cylinderInterior r (d / 4)
    let M := sourceSup v r
    let γ := (3 / 2 : ℝ) - 5 * ε
    let H := (radiusAffineSeminorm (sourceExpansion v Y Z) Q γ (d / 4)).toReal
    d * (localScalarSup (fun x => ‖sourceAffineCoefficient v Y Z x‖) D).toReal ≤
      72 * (d ^ γ * H + M) := by
  let Q := Local.cylinderInterior r (d / 4)
  let ν := sourceAffineCoefficient v Y Z
  have hh := source_parent_quarter_all_cutoffs_positive v Y Z hv hY hZ d hr hr1 hd
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscale
  have hD : Local.cylinderInterior r d ⊆ Q :=
    Local.cylinderInterior_mono (by positivity) (by linarith)
  have hQ : Q ⊆ Metric.closedBall 0 1 :=
    mixedInterior_subset_unit_closedBall hr (by positivity)
  have hνc := (sourceAffineCoefficient_contDiff v Y Z hv hY hZ).continuous
  have hb : BddAbove ((fun x => ‖ν x‖) '' Q) :=
    ((isCompact_closedBall (0 : ParabolicSpace) 1).image_of_continuousOn
      hνc.norm.continuousOn).bddAbove.mono (Set.image_mono hQ)
  have hN : 0 ≤ sSup ((fun x => ‖ν x‖) '' Q) := by
    obtain ⟨x, hx⟩ := hne.mono hD
    exact (norm_nonneg _).trans (le_csSup hb ⟨x, hx, rfl⟩)
  have hsup : localScalarSup (fun x => ‖ν x‖) (Local.cylinderInterior r d) ≤
      ENNReal.ofReal (sSup ((fun x => ‖ν x‖) '' Q)) := by
    simp only [localScalarSup, iSup_le_iff]
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    simpa only [abs_of_nonneg (norm_nonneg _)] using le_csSup hb ⟨x, hD hx, rfl⟩
  have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
  rw [ENNReal.toReal_ofReal hN] at hn
  exact (mul_le_mul_of_nonneg_left hn hd.le).trans hh.1


end GlobalPhi43.MW20
