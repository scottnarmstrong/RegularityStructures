module

public import GlobalPhi43.MW20.InfiniteKernel

/-!
# Positivity of the constructed finite and infinite densities
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction

/-- The finite averages remain nonnegative. -/
theorem finiteKernelDensity_nonneg (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (n : ℕ) (x : ParabolicSpace) :
    0 ≤ finiteKernelDensity Φ hΦ T hT n x := by
  have := kernelProfileMeasure_probability Φ hΦ
  induction n generalizing x with
  | zero =>
    simp only [finiteKernelDensity, convolutionIter, scaledKernelSeed_apply]
    exact mul_nonneg (by positivity) (hΦ.nonneg _)
  | succ n ih =>
    change 0 ≤ ∫ y, finiteKernelDensity Φ hΦ T hT n (x - y)
      ∂dyadicKernelFactor (kernelProfileMeasure Φ) (T / 2) n
    exact integral_nonneg fun y => ih (x - y)

/-- Nonnegativity passes to the constructed uniform limit. -/
theorem infiniteKernel_nonneg (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (x : ParabolicSpace) :
    0 ≤ infiniteKernel Φ hΦ T hT x := by
  have ht := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (finiteKernelDensity_tendsto Φ hΦ hT hT1)).tendsto_at x
  exact ge_of_tendsto ht (Filter.Eventually.of_forall fun n =>
    finiteKernelDensity_nonneg Φ hΦ hT n x)

/-- Every finite average contracts the norm of its first factor. -/
theorem norm_finiteKernelDensity_le (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ‖finiteKernelDensity Φ hΦ T hT n‖ ≤ ‖scaledKernelSeed Φ hΦ (T / 2) (half_pos hT)‖ := by
  have := kernelProfileMeasure_probability Φ hΦ
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (norm_probabilityConvolution_le _ _).trans ih

end GlobalPhi43.MW20
