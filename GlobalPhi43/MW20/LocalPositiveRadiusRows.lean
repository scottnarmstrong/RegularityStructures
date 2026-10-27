module

public import GlobalPhi43.MW20.LocalPositiveRadiusIncrement
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.LocalSourceHolder
public import Mathlib.Basic.ENNReal.Real
public import GlobalPhi43.MW20.SourceConeEstimate
public import GlobalPhi43.MW20.RadiusCoefficientSup
public import GlobalPhi43.MW20.CylinderCoefficientBounds
public import GlobalPhi43.MW20.SourceAffineCoefficient
public import GlobalPhi43.Local.SchauderInputs
public import GlobalPhi43.MW20.ScalarHolderSeminorm
public import GlobalPhi43.MW20.ParentHolderNorm
public import GlobalPhi43.MW20.ParentExpansionIncrement
public import GlobalPhi43.MW20.RadiusAffineSeminorm
public import GlobalPhi43.MW20.ParentInterpolationAlgebra
public import GlobalPhi43.MW20.ParentHolderCutoff

/-! Localized parent-amplitude estimates in terms of local positive-tree norms,
with the norms taken on the specified local domains. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem source_parent_radius_coefficient_row_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d α β c : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : 0 < d) (hcone : d ≤ 1 / 2 - d)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 1 < α + β) (hc : 0 ≤ c)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hfinite : radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) (α + β) d ≠ ⊤)
    (hbudgetY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * sourceSup v r ^ β))
    (hbudgetZ : parabolicHolderSeminorm α (parabolicClosedNbhd mwCylinder 1) Z ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 + α))) :
    BddAbove ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' Local.cylinderInterior r d) ∧
      sSup ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' Local.cylinderInterior r d) ≤
        6 * ((radiusAffineSeminorm (sourceExpansion v Y Z)
          (Local.cylinderInterior r d) (α + β) d).toReal * d ^ (α + β - 1) +
          d ^ (-1 : ℝ) * sourceSup v r +
          c * d ^ (α - 1) * sourceSup v r ^ (1 + α) +
          c * d ^ (β - 1) * sourceSup v r ^ (1 + β)) := by
  have hvreg := sourceCubicRegularity_of_contDiff (hv.of_le (by simp))
  have hM := sourceSup_nonneg_of_continuousOn_all hvreg.continuous hr
  have hsup := source_expansion_parent_two_point_positive hvreg hr hd hα hβ hc hbudgetY hbudgetZ
  have hA : radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) (α + β) d ≤ ENNReal.ofReal
        (radiusAffineSeminorm (sourceExpansion v Y Z)
          (Local.cylinderInterior r d) (α + β) d).toReal := by
    rw [ENNReal.ofReal_toReal hfinite]
  have hh := radius_cone_coefficient_sup (sourceExpansion v Y Z)
    (sourceExpansion_contDiff v Y Z hv hY hZ) _ (isOpen_cylinderInterior r d) hne hγ
    hd hd hcone (le_refl d) ENNReal.toReal_nonneg (by positivity) hA hsup
    (cylinderInterior_spatialInteriorCone hr1)
  change BddAbove ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' _) ∧ _ at hh
  refine ⟨hh.1, ?_⟩
  have he (a : ℝ) : d ^ a / d = d ^ (a - 1) := by
    rw [Real.rpow_sub hd, Real.rpow_one]
  have hB : (2 * sourceSup v r + c * d ^ α * sourceSup v r ^ (1 + α) +
      3 * c * d ^ β * sourceSup v r ^ (1 + β)) / d =
      2 * d ^ (-1 : ℝ) * sourceSup v r +
        c * d ^ (α - 1) * sourceSup v r ^ (1 + α) +
        3 * c * d ^ (β - 1) * sourceSup v r ^ (1 + β) := by
    calc
      _ = 2 * (sourceSup v r / d) + c * (d ^ α / d) * sourceSup v r ^ (1 + α) +
          3 * c * (d ^ β / d) * sourceSup v r ^ (1 + β) := by ring
      _ = _ := by rw [he, he, Real.rpow_neg_one]; ring
  have hbound := hh.2
  change (1 / 2 : ℝ) * sSup ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' Local.cylinderInterior r d) ≤ _ at hbound
  rw [hB] at hbound
  have h₁ : 0 ≤ (radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) (α + β) d).toReal * d ^ (α + β - 1) := by positivity
  have h₂ : 0 ≤ d ^ (-1 : ℝ) * sourceSup v r := by positivity
  have h₃ : 0 ≤ c * d ^ (α - 1) * sourceSup v r ^ (1 + α) := by positivity
  nlinarith only [hbound, h₁, h₂, h₃]


theorem source_parent_radius_interpolation_rows_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d α β c : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : 0 < d) (hcone : d ≤ 1 / 2 - d)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α ≤ β) (hβ1 : β ≤ 1)
    (hγ : 1 < α + β) (hc : 0 ≤ c)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hfinite : radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) (α + β) d ≠ ⊤)
    (hbudgetY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * sourceSup v r ^ β))
    (hbudgetZ : parabolicHolderSeminorm α (parabolicClosedNbhd mwCylinder 1) Z ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 + α))) :
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) d).toReal
    let N := sSup ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' D)
    N ≤ 6 * (H * d ^ (α + β - 1) + d ^ (-1 : ℝ) * M +
      c * d ^ (α - 1) * M ^ (1 + α) + c * d ^ (β - 1) * M ^ (1 + β)) ∧
    localSourceHolder (fun x => v x + Z x) β D d ≤
      24 * (d ^ α * H + d ^ (-β) * M + c * M ^ (1 + β) +
        c * d ^ (α - β) * M ^ (1 + α)) ∧
    localSourceHolder v α D d ≤
      24 * (d ^ β * H + d ^ (-α) * M + c * M ^ (1 + α) +
        c * d ^ (β - α) * M ^ (1 + β)) := by
  let D := Local.cylinderInterior r d
  let M := sourceSup v r
  let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) d).toReal
  let N := sSup ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' D)
  have hvreg := sourceCubicRegularity_of_contDiff (hv.of_le (by simp))
  have hM : 0 ≤ M := sourceSup_nonneg_of_continuousOn_all hvreg.continuous hr
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hNr := source_parent_radius_coefficient_row_positive v Y Z hv hY hZ hr hr1 hd hcone
    hα hβ hγ hc hne hfinite hbudgetY hbudgetZ
  have hν : ∀ x ∈ D, ‖sourceAffineCoefficient v Y Z x‖ ≤ N := by
    intro x hx
    exact le_csSup hNr.1 ⟨x, hx, rfl⟩
  have hN : 0 ≤ N := by
    obtain ⟨x, hx⟩ := hne
    exact (norm_nonneg _).trans (hν x hx)
  have hU : radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) d ≤ ENNReal.ofReal H := by
    dsimp only [H]
    rw [ENNReal.ofReal_toReal hfinite]
  have hvD : ∀ x ∈ D, |v x| ≤ M := by
    intro x hx
    exact abs_le_sourceSup_of_continuousOn hvreg.continuous hr (mixedInterior_subset_base hd.le hx)
  have hs := source_parent_radius_sum_holder_positive v Y Z hv hY hZ D (isOpen_cylinderInterior r d)
    (mixedInterior_subset_positive hr hd.le) hd hα hβ hβ1 hγ hH hN hM hc hU hν hbudgetY hvD
  have ht := source_parent_radius_v_holder_positive v Y Z hv hY hZ D (isOpen_cylinderInterior r d)
    (mixedInterior_subset_positive hr hd.le) hd hβ hαβ (hαβ.trans hβ1) hγ hH hN hM hc hU hν hbudgetY hbudgetZ hvD
  have hn : N ≤ 6 * (H * d ^ (α + β - 1) + d ^ (-1 : ℝ) * M +
      c * d ^ (α - 1) * M ^ (1 + α) + c * d ^ (β - 1) * M ^ (1 + β)) := hNr.2
  refine ⟨hn, ?_, ?_⟩
  · have hn' : N ≤ 6 * (H * d ^ (β + α - 1) + d ^ (-1 : ℝ) * M +
        c * d ^ (β - 1) * M ^ (1 + β) + c * d ^ (α - 1) * M ^ (1 + α)) := by
      rw [show β + α - 1 = α + β - 1 by ring]
      nlinarith only [hn]
    apply parent_interpolation_substitution hd hM hc hH hn'
    have he : 0 ≤ 3 * c * d ^ (α - β) * M ^ (1 + α) := by positivity
    nlinarith only [hs, he]
  · apply parent_interpolation_substitution hd hM hc hH hn
    have he : 0 ≤ c * M ^ (1 + α) := by positivity
    nlinarith only [ht, he]


theorem localSourceHolder_sum_extend_parent_positive {v Z : ParabolicSpace → ℝ}
    {D : Set ParabolicSpace} {a b ρ L B M c : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hb0 : 0 ≤ b) (hab : a ≤ b)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hbounded : BddAbove (localSourceHolderValues (fun x => v x + Z x) b D ρ))
    (hnear : localSourceHolder (fun x => v x + Z x) b D ρ ≤ B)
    (hamp : ∀ x ∈ D, |v x| ≤ M)
    (hpos : D ⊆ parabolicClosedNbhd mwCylinder 1)
    (hZ : parabolicHolderSeminorm a (parabolicClosedNbhd mwCylinder 1) Z ≤ ENNReal.ofReal (c * M ^ (1 + a))) :
    localSourceHolder (fun x => v x + Z x) b D L ≤
      B + 2 * M * ρ ^ (-b) + c * M ^ (1 + a) * ρ ^ (a - b) := by
  apply localSourceHolder_le_of_increment (by positivity)
  intro x hx y hy hs _
  by_cases hn : Local.pdist x y ≤ ρ
  · have hi := (localSourceHolder_increment hbounded hx hy hn hρ1).trans
      (mul_le_mul_of_nonneg_right hnear (Real.rpow_nonneg hs.le b))
    have hp : 0 ≤ (2 * M * ρ ^ (-b) + c * M ^ (1 + a) * ρ ^ (a - b)) *
        Local.pdist x y ^ b := by positivity
    nlinarith only [hi, hp]
  · have hv : |v y - v x| ≤ 2 * M := (abs_sub _ _).trans
      (by linarith [hamp x hx, hamp y hy])
    have hz := abs_sub_le_of_parabolicHolderSeminorm_le (show 0 ≤ c * M ^ (1 + a) by positivity) hZ (hpos hx) (hpos hy)
    have hi : |(v y + Z y) - (v x + Z x)| ≤
        2 * M + c * M ^ (1 + a) * Local.pdist x y ^ a := by
      calc
        _ = |(v y - v x) + (Z y - Z x)| := by congr 1; ring
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add hv hz)
    have hp := mul_le_mul_of_nonneg_left
      (parent_holder_far_power hρ (le_of_not_ge hn) hb0) (show 0 ≤ 2 * M by positivity)
    have hq := mul_le_mul_of_nonneg_left
      (parent_holder_far_power hρ (le_of_not_ge hn) hab) (show 0 ≤ c * M ^ (1 + a) by positivity)
    simp only [Real.rpow_zero, zero_sub] at hp
    have hbase : 0 ≤ B * Local.pdist x y ^ b := by positivity
    nlinarith only [hi, hp, hq, hbase]


theorem source_parent_radius_all_cutoffs_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d α β c L : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : 0 < d) (hcone : d ≤ 1 / 2 - d)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α ≤ β) (hβ1 : β ≤ 1)
    (hγ : 1 < α + β) (hc : 0 ≤ c)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hfinite : radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) (α + β) d ≠ ⊤)
    (hbudgetY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * sourceSup v r ^ β))
    (hbudgetZ : parabolicHolderSeminorm α (parabolicClosedNbhd mwCylinder 1) Z ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 + α))) :
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) d).toReal
    localSourceHolder (fun x => v x + Z x) β D L ≤
      26 * (d ^ α * H + d ^ (-β) * M + c * M ^ (1 + β) +
        c * d ^ (α - β) * M ^ (1 + α)) ∧
    localSourceHolder v α D L ≤
      26 * (d ^ β * H + d ^ (-α) * M + c * M ^ (1 + α) +
        c * d ^ (β - α) * M ^ (1 + β)) := by
  let D := Local.cylinderInterior r d
  let M := sourceSup v r
  let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) d).toReal
  have hrows := source_parent_radius_interpolation_rows_positive v Y Z hv hY hZ hr hr1 hd hcone
    hα hβ hαβ hβ1 hγ hc hne hfinite hbudgetY hbudgetZ
  have hvreg := sourceCubicRegularity_of_contDiff (hv.of_le (by simp))
  have hsumreg := sourceCubicRegularity_of_contDiff ((hv.add hZ).of_le (by simp))
  have hM : 0 ≤ M := sourceSup_nonneg_of_continuousOn_all hvreg.continuous hr
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hd1 : d ≤ 1 := by linarith
  have hvD : ∀ x ∈ D, |v x| ≤ M := by
    intro x hx
    exact abs_le_sourceSup_of_continuousOn hvreg.continuous hr (mixedInterior_subset_base hd.le hx)
  have hbV := mixedInteriorHolder_bddAbove hvreg hr hd (hαβ.trans hβ1) hd1
  have hbS := mixedInteriorHolder_bddAbove hsumreg hr hd hβ1 hd1
  have hve := localSourceHolder_extend_parent (L := L) hd hd1 hα (by positivity) hM
    hbV hrows.2.2 hvD
  have hse := localSourceHolder_sum_extend_parent_positive (L := L) hd hd1 hβ hαβ
    (by positivity) hM hc hbS hrows.2.1 hvD (mixedInterior_subset_positive hr hd.le) hbudgetZ
  refine ⟨?_, ?_⟩
  · have hrest : 0 ≤ 2 * d ^ α * H + 2 * c * M ^ (1 + β) +
        c * d ^ (α - β) * M ^ (1 + α) := by positivity
    nlinarith only [hse, hrest]
  · have hrest : 0 ≤ d ^ β * H + c * M ^ (1 + α) +
        c * d ^ (β - α) * M ^ (1 + β) := by positivity
    nlinarith only [hve, hrest]


theorem source_parent_radius_weighted_all_cutoffs_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d α β c L : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : 0 < d) (hcone : d ≤ 1 / 2 - d)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α ≤ β) (hβ1 : β ≤ 1)
    (hγ : 1 < α + β) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hfinite : radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) (α + β) d ≠ ⊤)
    (hbudgetY : parabolicHolderSeminorm β (parabolicClosedNbhd mwCylinder 1) Y ≤ ENNReal.ofReal (c * sourceSup v r ^ β))
    (hbudgetZ : parabolicHolderSeminorm α (parabolicClosedNbhd mwCylinder 1) Z ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 + α)))
    (hMpos : 0 < sourceSup v r) (hscale : d * sourceSup v r ≤ 1) :
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) d).toReal
    let N := sSup ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' D)
    d * N ≤ 18 * (d ^ (α + β) * H + M) ∧
    d ^ β * localSourceHolder (fun x => v x + Z x) β D L ≤
      78 * (d ^ (α + β) * H + M) ∧
    d ^ α * localSourceHolder v α D L ≤ 78 * (d ^ (α + β) * H + M) := by
  let D := Local.cylinderInterior r d
  let M := sourceSup v r
  let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D (α + β) d).toReal
  let N := sSup ((fun x => ‖sourceAffineCoefficient v Y Z x‖) '' D)
  have hrc := source_parent_radius_coefficient_row_positive v Y Z hv hY hZ hr hr1 hd hcone
    hα hβ hγ hc hne hfinite hbudgetY hbudgetZ
  have hhr := source_parent_radius_all_cutoffs_positive (L := L) v Y Z hv hY hZ hr hr1 hd hcone
    hα hβ hαβ hβ1 hγ hc hne hfinite hbudgetY hbudgetZ
  have hh := And.intro hrc.2 hhr
  change N ≤ 6 * (H * d ^ (α + β - 1) + d ^ (-1 : ℝ) * M +
    c * d ^ (α - 1) * M ^ (1 + α) + c * d ^ (β - 1) * M ^ (1 + β)) ∧
    localSourceHolder (fun x => v x + Z x) β D L ≤
      26 * (d ^ α * H + d ^ (-β) * M + c * M ^ (1 + β) +
        c * d ^ (α - β) * M ^ (1 + α)) ∧
    localSourceHolder v α D L ≤
      26 * (d ^ β * H + d ^ (-α) * M + c * M ^ (1 + α) +
        c * d ^ (β - α) * M ^ (1 + β)) at hh
  have hn : N ≤ 6 * (d ^ (α + β - 1) * H + d ^ (-1 : ℝ) * M +
      c * d ^ (α - 1) * M ^ (1 + α) + c * d ^ (β - 1) * M ^ (1 + β)) := by
    simpa only [mul_comm H] using hh.1
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hnw := parent_coefficient_weight hd hMpos hc hc1 hα hβ hH (by norm_num) hscale hn
  have hsw := parent_holder_weight hd hMpos hc hc1 hβ hα hH (by norm_num) hscale hh.2.1
  have hvw := parent_holder_weight hd hMpos hc hc1 hα hβ hH (by norm_num) hscale hh.2.2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [show (3 : ℝ) * 6 = 18 by norm_num] using hnw
  · simpa only [show (3 : ℝ) * 26 = 78 by norm_num, show β + α = α + β by ring] using hsw
  · simpa only [show (3 : ℝ) * 26 = 78 by norm_num] using hvw


end GlobalPhi43.MW20
