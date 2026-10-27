module

public import GlobalPhi43.MW20.InfiniteKernelSupport
public import GlobalPhi43.MW20.InfiniteKernelBlock
public import GlobalPhi43.MW20.ConvolutionPairing

/-!
# Identification of the finite density with the finite MW20 measure
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures
open scoped BoundedContinuousFunction

/-- The actual finite Lebesgue density represents the finite dyadic convolution
measure, with n+1 factors; the measure zero-step convention remains Dirac. -/
theorem integral_finiteKernelDensity_mul (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (n : ℕ) (g : ParabolicSpace →ᵇ ℝ) :
    (∫ x, finiteKernelDensity Φ hΦ T hT n x * g x) =
      ∫ x, g x ∂dyadicKernelMeasure (kernelProfileMeasure Φ) T (n + 1) := by
  have := kernelProfileMeasure_probability Φ hΦ
  induction n generalizing g with
  | zero =>
    have h := integral_scaledKernelMeasure Φ hΦ (half_pos hT) g
    simpa only [finiteKernelDensity, convolutionIter, scaledKernelSeed,
      compactSmoothSeed_apply, dyadicKernelMeasure_one, dyadicKernelFactor,
      Nat.zero_add, pow_one] using h.symm
  | succ n ih =>
    have hk := (finiteKernelDensity Φ hΦ T hT n).continuous.integrable_of_hasCompactSupport (μ := volume)
      (finiteKernelDensity_hasCompactSupport Φ hΦ hT hT1 n)
    change (∫ x, probabilityConvolution
      (dyadicKernelFactor (kernelProfileMeasure Φ) (T / 2) n)
      (finiteKernelDensity Φ hΦ T hT n) x * g x) = _
    rw [integral_probabilityConvolution_mul _ _ _ hk]
    have hm : dyadicKernelMeasure (kernelProfileMeasure Φ) T (n + 1 + 1) =
        (dyadicKernelFactor (kernelProfileMeasure Φ) (T / 2) n).conv
          (dyadicKernelMeasure (kernelProfileMeasure Φ) T (n + 1)) := by
      rw [dyadicKernelMeasure, kernelMeasure]
      simp only [Nat.zero_add]
      change (dyadicKernelMeasure (kernelProfileMeasure Φ) T (n + 1)).conv
        (dyadicKernelFactor (kernelProfileMeasure Φ) T (n + 1)) = _
      rw [dyadicKernelFactor_succ, Measure.conv_comm]
    rw [hm, integral_conv (g.integrable _)]
    apply integral_congr_ae
    apply ae_of_all
    intro y
    simpa only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
      add_comm y] using ih
      (g.compContinuous ⟨fun x => x + y, continuous_id.add continuous_const⟩)

end GlobalPhi43.MW20
