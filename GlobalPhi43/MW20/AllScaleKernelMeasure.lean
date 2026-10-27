module

public import GlobalPhi43.MW20.AllScaleKernel
public import GlobalPhi43.MW20.KernelPastSupport

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures
open scoped ContDiff BoundedContinuousFunction

/-- Positivity of the same constructed density at every positive scale. -/
theorem infiniteKernel_nonneg_all (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (y : ParabolicSpace) : 0 ≤ infiniteKernel Φ hΦ T hT y := by
  rw [infiniteKernel_eq_rescaled_unit_all Φ hΦ hT]
  exact mul_nonneg (by positivity) (infiniteKernel_nonneg Φ hΦ (by norm_num) le_rfl _)

/-- Compact support is transported from the actual unit density. -/
theorem infiniteKernel_hasCompactSupport_all (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) : HasCompactSupport (infiniteKernel Φ hΦ T hT) := by
  have hs := (infiniteKernel_hasCompactSupport Φ hΦ (by norm_num : (0 : ℝ)<1) le_rfl).comp_homeomorph (parabolicKernelHomeomorph T⁻¹ (inv_ne_zero hT.ne'))
  have hc := hs.mul_left (f := fun _ : ParabolicSpace => (T^5)⁻¹)
  convert hc using 1
  funext y
  exact infiniteKernel_eq_rescaled_unit_all Φ hΦ hT y

/-- The actual measure/density identity has no upper-scale restriction. -/
theorem integral_infiniteKernelMeasure_all (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (g : ParabolicSpace → ℝ) :
    (∫ y, g y ∂infiniteKernelMeasure Φ hΦ T hT) =
      ∫ y, infiniteKernel Φ hΦ T hT y*g y := by
  unfold infiniteKernelMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun y => ENNReal.ofReal (infiniteKernel Φ hΦ T hT y))
    (ENNReal.measurable_ofReal.comp (infiniteKernel Φ hΦ T hT).continuous.measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (infiniteKernel_nonneg_all Φ hΦ hT _),smul_eq_mul]

end GlobalPhi43.MW20
