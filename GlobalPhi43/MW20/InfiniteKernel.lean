module

public import GlobalPhi43.MW20.ScaledKernelSeed
public import GlobalPhi43.MW20.DyadicConvolutionLimit

/-!
# The infinite smooth MW20 kernel

The first factor is the actual density Φ at scale T/2. All remaining factors
are the actual parabolic pushforwards of the profile probability measure.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction ContDiff NNReal

/-- The finite density with its first factor singled out. Index zero already
contains Φ at scale T/2; the remaining n factors have scales T/4,... . -/
@[expose] noncomputable def finiteKernelDensity (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (T : ℝ) (hT : 0 < T) (n : ℕ) : ParabolicSpace →ᵇ ℝ :=
  letI := kernelProfileMeasure_probability Φ hΦ
  convolutionIter (dyadicKernelFactor (kernelProfileMeasure Φ) (T / 2))
    (scaledKernelSeed Φ hΦ (T / 2) (half_pos hT)) n

/-- The infinite density is constructed as the uniform-norm limit of its
finite convolutions. No convergence hypothesis is part of this definition. -/
@[expose] noncomputable def infiniteKernel (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (T : ℝ) (hT : 0 < T) : ParabolicSpace →ᵇ ℝ :=
  letI := kernelProfileMeasure_probability Φ hΦ
  convolutionLimit (dyadicKernelFactor (kernelProfileMeasure Φ) (T / 2))
    (scaledKernelSeed Φ hΦ (T / 2) (half_pos hT))

/-- Uniform convergence of the finite densities at every source scale. -/
theorem finiteKernelDensity_tendsto (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    Tendsto (finiteKernelDensity Φ hΦ T hT) atTop (𝓝 (infiniteKernel Φ hΦ T hT)) := by
  have := kernelProfileMeasure_probability Φ hΦ
  obtain ⟨K, hK⟩ := compactSmoothSeed_lipschitz (scaledKernelProfile Φ (T / 2))
    (scaledKernelProfile_smooth hΦ _) (scaledKernelProfile_compact hΦ (half_pos hT))
  exact dyadic_convolutionIter_tendsto _ _ hK (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 ≤ T / 2) (by linarith : T / 2 ≤ 1)
    (kernelProfileMeasure_ae_norm_le Φ hΦ)

/-- The limit density is smooth to every order, as a consequence of convergence
of the actual derivative convolutions of the compact smooth first factor. -/
theorem infiniteKernel_contDiff (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    ContDiff ℝ ∞ (infiniteKernel Φ hΦ T hT) := by
  have := kernelProfileMeasure_probability Φ hΦ
  exact convolutionLimit_compactSmooth_contDiff _ _
    (scaledKernelProfile_smooth hΦ _) (scaledKernelProfile_compact hΦ (half_pos hT))
    (by positivity : 0 ≤ (T / 2) * 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (dyadicKernelFactor_ae_norm_le _ (by positivity : 0 ≤ T / 2)
      (by linarith : T / 2 ≤ 1) (kernelProfileMeasure_ae_norm_le Φ hΦ))

end GlobalPhi43.MW20
