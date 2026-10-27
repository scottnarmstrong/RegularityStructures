module

public import GlobalPhi43.MW20.SourceWeightedAffineFiniteness
public import GlobalPhi43.Local.RadiusNormAssembly

/-! Finiteness and scale extraction for the weighted radius supremum. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff ENNReal

/-- The weighted radius supremum is finite on any fixed cutoff d0. Compact
Taylor constants prove finiteness only and do not enter quantitative rows. -/
theorem source_weightedRadiusAffineSeminorm_ne_top
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d₀ γ : ℝ} (hr : 0 ≤ r) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) :
    Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ ≠ ⊤ := by
  obtain ⟨C, _, hC⟩ := source_expansion_uniform_radius_bound v Y Z hv hY hZ hr hγ hγ2
  apply ne_top_of_le_ne_top (b := ENNReal.ofReal (max 1 (d₀ ^ γ)) * ENNReal.ofReal C)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  simp only [Local.weightedRadiusAffineSeminorm, iSup_le_iff]
  intro d hd
  have hp : d ^ γ ≤ max 1 (d₀ ^ γ) :=
    (Real.rpow_le_rpow hd.1.le hd.2 hγ).trans (le_max_right _ _)
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hp) (hC d hd.1.le d)

/-- Extract each actual weighted radius norm from the finite weighted radius
supremum. The scale cutoff remains d0 rather than being enlarged to one. -/
theorem source_weightedRadiusAffineSeminorm_scale_bound
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d₀ d γ : ℝ} (hr : 0 ≤ r) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2)
    (hd : d ∈ Ioc (0 : ℝ) d₀) :
    d ^ γ * (radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) γ d).toReal ≤
        (Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ).toReal := by
  have hf := source_weightedRadiusAffineSeminorm_ne_top v Y Z hv hY hZ (d₀ := d₀) hr hγ hγ2
  have hle : ENNReal.ofReal (d ^ γ) * radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r d) γ d ≤
      Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ :=
    le_iSup_of_le d (le_iSup_of_le hd le_rfl)
  have hh := ENNReal.toReal_mono hf hle
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hd.1.le γ)] using hh

/-- The actual quarter-scale norm costs exactly 4^gamma while preserving
both the outer d-weight and the original supremum cutoff d0. -/
theorem source_weightedRadiusAffineSeminorm_quarter_bound
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d₀ d γ : ℝ} (hr : 0 ≤ r) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2)
    (hd : d ∈ Ioc (0 : ℝ) d₀) :
    d ^ γ * (radiusAffineSeminorm (sourceExpansion v Y Z)
      (Local.cylinderInterior r (d / 4)) γ (d / 4)).toReal ≤
        (4 : ℝ) ^ γ *
          (Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ).toReal := by
  have hq : d / 4 ∈ Ioc (0 : ℝ) d₀ := ⟨by linarith [hd.1], by linarith [hd.1, hd.2]⟩
  have hh := source_weightedRadiusAffineSeminorm_scale_bound v Y Z hv hY hZ hr hγ hγ2 hq
  have hdpos := hd.1
  have he : d ^ γ = (4 : ℝ) ^ γ * (d / 4) ^ γ := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : 0 ≤ d / 4)]
    congr 1
    ring
  rw [he, mul_assoc]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

end GlobalPhi43.MW20
