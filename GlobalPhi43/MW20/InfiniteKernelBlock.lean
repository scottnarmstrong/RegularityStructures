module

public import GlobalPhi43.MW20.InfiniteKernelRecursion

/-!
# Exact infinite dyadic block identity
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures
open scoped BoundedContinuousFunction

/-- Zero factors act as the identity on every bounded continuous field. -/
theorem probabilityConvolution_dirac_zero (f : ParabolicSpace →ᵇ ℝ) :
    probabilityConvolution (Measure.dirac 0) f = f := by
  ext x
  simp only [probabilityConvolution_apply, integral_dirac, sub_zero]

/-- One finite dyadic factor is the corresponding actual pushforward. -/
theorem dyadicKernelMeasure_one (μ : Measure ParabolicSpace) [IsProbabilityMeasure μ] (T : ℝ) :
    dyadicKernelMeasure μ T 1 = dyadicKernelFactor μ T 0 := by
  simp [dyadicKernelMeasure, kernelMeasure]

/-- MW20 (2.8), as an identity of the constructed smooth densities. -/
theorem infiniteKernel_block (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (n : ℕ) :
    letI := kernelProfileMeasure_probability Φ hΦ
    infiniteKernel Φ hΦ T hT =
      probabilityConvolution (dyadicKernelMeasure (kernelProfileMeasure Φ) T n)
        (infiniteKernel Φ hΦ (T / 2 ^ n) (div_pos hT (by positivity))) := by
  have := kernelProfileMeasure_probability Φ hΦ
  induction n generalizing T with
  | zero =>
    simpa only [pow_zero, div_one, dyadicKernelMeasure, kernelMeasure] using
      (probabilityConvolution_dirac_zero (infiniteKernel Φ hΦ T hT)).symm
  | succ n ih =>
    have hh : 0 < T / 2 := half_pos hT
    have hh1 : T / 2 ≤ 1 := by linarith
    rw [infiniteKernel_recursion Φ hΦ hT hT1, ih hh hh1]
    rw [← probabilityConvolution_conv]
    have hscale : T / 2 / 2 ^ n = T / 2 ^ (n + 1) := by
      rw [pow_succ]; ring
    have hm : dyadicKernelMeasure (kernelProfileMeasure Φ) T (n + 1) =
        (dyadicKernelFactor (kernelProfileMeasure Φ) T 0).conv
          (dyadicKernelMeasure (kernelProfileMeasure Φ) (T / 2) n) := by
      simpa only [pow_one, dyadicKernelMeasure_one, Nat.add_comm 1 n] using
        dyadicKernelMeasure_add (kernelProfileMeasure Φ) T 1 n
    ext x
    simp only [probabilityConvolution_apply]
    simp only [hm, hscale]

end GlobalPhi43.MW20
