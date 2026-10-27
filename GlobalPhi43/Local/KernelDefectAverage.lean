/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.DefectSmoothing
public import GlobalPhi43.Local.DefectBudget
public import GlobalPhi43.Local.SmallScaleLocalData
public import GlobalPhi43.Local.SourceSectionHeat

/-! The signed defects averaged by the actual native kernel, using only
suprema on the original P-plus and the parent cylinder amplitude. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set

 theorem kernel_defect_average_bound
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v e₁ e₂ e₃ : ParabolicSpace → ℝ) (hv : Continuous v)
    {r d L T E₁ E₂ E₃ : ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L)
    (hT : 0 < T) (hT₁ : T ≤ 1) (hLT : L + T ≤ d)
    (hE₂ : 0 ≤ E₂)
    (he₁ : ∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₁ z| ≤ E₁)
    (he₂ : ∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₂ z| ≤ E₂)
    (he₃ : ∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₃ z| ≤ E₃)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d) (hy : y ∈ pastBall x L) :
    |∫ w, -e₁ (y + w) + e₃ (y + w) + 3 * v x * e₂ (y + w)
      ∂infiniteKernelMeasure Φ hΦ T hT| ≤ E₁ + E₃ + 3 * sourceSup v r * E₂ := by
  have := infiniteKernelMeasure_probability Φ hΦ hT hT₁
  have hxD := cylinderInterior_mem_domain (by linarith : 0 ≤ d) hx
  have hvx := abs_le_sourceSup hv hr hxD
  have hsample : ∀ᵐ w ∂infiniteKernelMeasure Φ hΦ T hT,
      y + w ∈ parabolicClosedNbhd mwCylinder 1 := by
    filter_upwards [infiniteKernelMeasure_ae_strictPast Φ hΦ hT hT₁] with w hw
    have hz := add_mem_pastBall_add hy hw.1.le hw.2
    have hzD := cylinderInterior_mem_domain (by norm_num : (0 : ℝ) ≤ 0)
      (pastBall_subset_interior (by norm_num : (0 : ℝ) ≤ 0)
        (by positivity : 0 ≤ L + T) (by linarith) hx hz)
    have hzP : y + w ∈ mwCylinder := by
      rw [mwCylinder_eq_sourceCylinder]
      exact sourceCylinder_antitone (by norm_num : (0 : ℝ) ≤ 0) hr hzD
    exact ⟨y + w, hzP, by simp [parabolicDist]⟩
  apply defect_average_bound _ (fun w => e₁ (y + w)) (fun w => e₂ (y + w))
    (fun w => e₃ (y + w)) _ _ _ hvx hE₂
  · filter_upwards [hsample] with w hw
    exact he₁ _ hw
  · filter_upwards [hsample] with w hw
    exact he₂ _ hw
  · filter_upwards [hsample] with w hw
    exact he₃ _ hw

end GlobalPhi43.Local
