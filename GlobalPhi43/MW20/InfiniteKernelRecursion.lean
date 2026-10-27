module

public import GlobalPhi43.MW20.InfiniteKernel
public import GlobalPhi43.MW20.ScaledKernelCommutation
public import GlobalPhi43.MW20.ConvolutionIteration

/-!
# The first-factor identity for the constructed MW20 density
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction

/-- Moving one step along the dyadic tail halves its starting scale. -/
theorem dyadicKernelFactor_succ (μ : Measure ParabolicSpace) (T : ℝ) (j : ℕ) :
    dyadicKernelFactor μ T (j + 1) = dyadicKernelFactor μ (T / 2) j := by
  simpa only [Nat.one_add, pow_one] using dyadicKernelFactor_shift μ T 1 j

/-- Exact first-factor identity for the actual finite densities. -/
theorem finiteKernelDensity_recursion (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    letI := kernelProfileMeasure_probability Φ hΦ
    finiteKernelDensity Φ hΦ T hT (n + 1) =
      probabilityConvolution (dyadicKernelFactor (kernelProfileMeasure Φ) T 0)
        (finiteKernelDensity Φ hΦ (T / 2) (half_pos hT) n) := by
  have := kernelProfileMeasure_probability Φ hΦ
  unfold finiteKernelDensity
  rw [convolutionIter_shift]
  have hfirst : probabilityConvolution
      (dyadicKernelFactor (kernelProfileMeasure Φ) (T / 2) 0)
      (scaledKernelSeed Φ hΦ (T / 2) (half_pos hT)) =
      probabilityConvolution (dyadicKernelFactor (kernelProfileMeasure Φ) T 0)
      (scaledKernelSeed Φ hΦ (T / 2 / 2) (half_pos (half_pos hT))) := by
    simpa only [dyadicKernelFactor, Nat.zero_add, pow_one] using
      probabilityConvolution_scaledSeeds_comm Φ hΦ (half_pos (half_pos hT)) (half_pos hT)
  rw [hfirst, convolutionIter_probabilityConvolution]
  congr 1
  congr 1
  funext j
  exact dyadicKernelFactor_succ _ _ j

/-- The source's infinite first-factor identity, proved by uniform convergence
and continuity of the actual averaging operator. -/
theorem infiniteKernel_recursion (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    letI := kernelProfileMeasure_probability Φ hΦ
    infiniteKernel Φ hΦ T hT =
      probabilityConvolution (dyadicKernelFactor (kernelProfileMeasure Φ) T 0)
        (infiniteKernel Φ hΦ (T / 2) (half_pos hT)) := by
  have := kernelProfileMeasure_probability Φ hΦ
  have hfull := (finiteKernelDensity_tendsto Φ hΦ hT hT1).comp (tendsto_add_atTop_nat 1)
  have htail := (probabilityConvolutionCLM
    (dyadicKernelFactor (kernelProfileMeasure Φ) T 0)).continuous.tendsto
    (infiniteKernel Φ hΦ (T / 2) (half_pos hT)) |>.comp
      (finiteKernelDensity_tendsto Φ hΦ (half_pos hT) (by linarith))
  apply tendsto_nhds_unique hfull
  convert! htail using 1
  funext n
  exact finiteKernelDensity_recursion Φ hΦ hT n

end GlobalPhi43.MW20
