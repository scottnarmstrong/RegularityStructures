/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AugmentedExpansionPDE
public import GlobalPhi43.Local.KernelDefectAverage
public import GlobalPhi43.MW20.GlobalHeatSmoothing
public import GlobalPhi43.MW20.CompactTestIntegral

/-! The actual smoothed expansion differs from the native zero-defect
forcing by only the original defect suprema and original parent mass. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set
open scoped ContDiff

 theorem localData_augmented_expansion_average
    {u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ} {C₁ C₂ E₁ E₂ E₃ : ℝ}
    (hd : IsMWLocalData u ζ J Y Z e₁ e₂ e₃ C₁ C₂) (hE₂ : 0 ≤ E₂)
    (he₁ : ∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₁ z| ≤ E₁)
    (he₂ : ∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₂ z| ≤ E₂)
    (he₃ : ∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₃ z| ≤ E₃) :
    ∃ (v : ParabolicSpace → ℝ) (W : Set ParabolicSpace),
      ContDiff ℝ ∞ v ∧ IsOpen W ∧ closure mwCylinder ⊆ W ∧
      EqOn v (fun z => u z - J z) W ∧
      ∀ (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
        (r d L T : ℝ) (hT : 0 < T), 0 ≤ r → 0 ≤ L → T ≤ 1 → L + T ≤ d →
      ∀ x ∈ cylinderInterior r d, ∀ y ∈ pastBall x L,
      |sourceHeat (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (expansion v Y Z x)) y -
        (∫ w, -v (y + w) ^ 3 - 3 * v (y + w) ^ 2 * J (y + w) -
          3 * (v (y + w) - v x) * (J (y + w) ^ 2 - C₁) -
          9 * C₂ * (v (y + w) + J (y + w)) ∂infiniteKernelMeasure Φ hΦ T hT)| ≤
        E₁ + E₃ + 3 * sourceSup (fun z => u z - J z) r * E₂ := by
  obtain ⟨v, W, hv, hW, hKW, heq, hpde⟩ := localData_augmented_expansion_PDE hd
  refine ⟨v, W, hv, hW, hKW, heq, ?_⟩
  intro Φ hΦ r d L T hT hr hL hT₁ hLT x hx y hy
  have := infiniteKernelMeasure_probability Φ hΦ hT hT₁
  let μ := infiniteKernelMeasure Φ hΦ T hT
  let F := fun z => -v z ^ 3 - 3 * v z ^ 2 * J z -
    3 * (v z - v x) * (J z ^ 2 - C₁) - 9 * C₂ * (v z + J z)
  let D := fun z => -e₁ z + e₃ z + 3 * v x * e₂ z
  have hsample : ∀ᵐ w ∂μ, y + w ∈ mwCylinder := by
    filter_upwards [infiniteKernelMeasure_ae_strictPast Φ hΦ hT hT₁] with w hw
    have hz := add_mem_pastBall_add hy hw.1.le hw.2
    have hzD := cylinderInterior_mem_domain (by norm_num : (0 : ℝ) ≤ 0)
      (pastBall_subset_interior (by norm_num : (0 : ℝ) ≤ 0)
        (by positivity : 0 ≤ L + T) (by linarith) hx hz)
    rw [mwCylinder_eq_sourceCylinder]
    exact sourceCylinder_antitone (by norm_num : (0 : ℝ) ≤ 0) hr hzD
  have hclosed : ∀ᵐ w ∂μ, y + w ∈ sourceClosedCylinder := by
    filter_upwards [hsample] with w hw
    rw [mwCylinder_eq_sourceCylinder] at hw
    exact sourceCylinder_subset_closed (by norm_num : (0 : ℝ) ≤ 0) hw
  have hvC := hv.continuous
  have hJC := hd.2.2.1.continuous
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hD : Continuous D := by
    dsimp [D]
    have he1 := hd.2.2.2.2.2.1.continuous
    have he2 := hd.2.2.2.2.2.2.1.continuous
    have he3 := hd.2.2.2.2.2.2.2.1.continuous
    fun_prop
  have hiF := integrable_comp_of_ae_mem_compact μ F isCompact_Icc hF.continuousOn
    (fun w => y + w) (continuous_const.add continuous_id) hclosed
  have hiD := integrable_comp_of_ae_mem_compact μ D isCompact_Icc hD.continuousOn
    (fun w => y + w) (continuous_const.add continuous_id) hclosed
  have he : (fun w => sourceHeat (expansion v Y Z x) (y + w)) =ᵐ[μ]
      (fun w => F (y + w) + D (y + w)) := by
    filter_upwards [hsample] with w hw
    rw [hpde x (y + w) hw]
    dsimp [F, D]
    ring
  have hU : ContDiff ℝ 2 (expansion v Y Z x) :=
    (source_expansion_contDiff_right v Y Z hv hd.2.2.2.1 hd.2.2.2.2.1 x).of_le (by simp)
  have hheat := sourceHeat_pastSmooth_global Φ hΦ hU hT hT₁ y
  change sourceHeat (pastSmooth μ (expansion v Y Z x)) y =
    (∫ w, sourceHeat (expansion v Y Z x) (y + w) ∂μ) at hheat
  rw [integral_congr_ae he, integral_add hiF hiD] at hheat
  have hb := kernel_defect_average_bound Φ hΦ v e₁ e₂ e₃ hv.continuous hr hL hT hT₁ hLT
    hE₂ he₁ he₂ he₃ hx hy
  rw [sourceSup_remainder_representative hKW heq hr] at hb
  change |sourceHeat (pastSmooth μ (expansion v Y Z x)) y - (∫ w, F (y + w) ∂μ)| ≤ _
  rw [hheat, add_sub_cancel_left]
  exact hb

end GlobalPhi43.Local
