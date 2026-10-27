module

public import GlobalPhi43.MW20.ScaledKernelSeed
public import GlobalPhi43.MW20.DyadicKernelMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The density of the actual parabolic pushforward
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures
open scoped BoundedContinuousFunction

/-- Integration against the profile measure is integration against Φ itself. -/
theorem integral_kernelProfileMeasure (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (g : ParabolicSpace → ℝ) :
    (∫ y, g y ∂kernelProfileMeasure Φ) = ∫ y, Φ y * g y := by
  unfold kernelProfileMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun z => ENNReal.ofReal (Φ z))
    (ENNReal.measurable_ofReal.comp hΦ.smooth.continuous.measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hΦ.nonneg _), smul_eq_mul]

/-- The pushed-forward measure has exactly the printed scaled density. -/
theorem integral_scaledKernelMeasure (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {c : ℝ} (hc : 0 < c) (g : ParabolicSpace →ᵇ ℝ) :
    (∫ y, g y ∂(kernelProfileMeasure Φ).map (parabolicDilate c)) =
      ∫ y, scaledKernelProfile Φ c y * g y := by
  rw [integral_map (measurable_parabolicDilate c).aemeasurable
    g.continuous.aestronglyMeasurable, integral_kernelProfileMeasure Φ hΦ]
  have heq : (fun y => scaledKernelProfile Φ c (parabolicDilate c y) * g (parabolicDilate c y)) =
      (fun y => (c ^ 5)⁻¹ * (Φ y * g (parabolicDilate c y))) := by
    funext y
    simp only [scaledKernelProfile, rescaledTestFunction, sub_zero,
      parabolicDilate_inv_parabolicDilate hc.ne']
    ring
  have hchange := integral_comp_parabolicDilate
    (fun y => scaledKernelProfile Φ c y * g y) hc
  rw [heq, integral_const_mul] at hchange
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 5 hc.ne')) hchange

end GlobalPhi43.MW20
