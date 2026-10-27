module

public import GlobalPhi43.MW20.KernelMass
public import GlobalPhi43.MW20.InfiniteKernelBlock
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# The actual infinite probability measure and its exact block factorisation
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures
open scoped BoundedContinuousFunction

/-- The actual measure associated with the constructed smooth MW20 density. -/
@[expose] noncomputable def infiniteKernelMeasure (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (T : ℝ) (hT : 0 < T) : Measure ParabolicSpace :=
  volume.withDensity (fun z => ENNReal.ofReal (infiniteKernel Φ hΦ T hT z))

/-- The infinite kernel measure is a probability measure. -/
theorem infiniteKernelMeasure_probability (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    IsProbabilityMeasure (infiniteKernelMeasure Φ hΦ T hT) := by
  constructor
  rw [infiniteKernelMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((infiniteKernel Φ hΦ T hT).continuous.integrable_of_hasCompactSupport
        (infiniteKernel_hasCompactSupport Φ hΦ hT hT1))
      (ae_of_all _ (infiniteKernel_nonneg Φ hΦ hT hT1)),
    integral_infiniteKernel Φ hΦ hT hT1]
  norm_num

/-- Exact density identification for arbitrary measurable or nonmeasurable
real fields; the integrals use the standard total Bochner convention. -/
theorem integral_infiniteKernelMeasure (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (g : ParabolicSpace → ℝ) :
    (∫ z, g z ∂infiniteKernelMeasure Φ hΦ T hT) =
      ∫ z, infiniteKernel Φ hΦ T hT z * g z := by
  unfold infiniteKernelMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun z => ENNReal.ofReal (infiniteKernel Φ hΦ T hT z))
    (ENNReal.measurable_ofReal.comp (infiniteKernel Φ hΦ T hT).continuous.measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (infiniteKernel_nonneg Φ hΦ hT hT1 _), smul_eq_mul]

/-- The exact infinite block identity for the actual probability measures.
This is the measure formulation used by the local reconstruction argument. -/
theorem infiniteKernelMeasure_block (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (n : ℕ) :
    infiniteKernelMeasure Φ hΦ T hT =
      (dyadicKernelMeasure (kernelProfileMeasure Φ) T n).conv
        (infiniteKernelMeasure Φ hΦ (T / 2 ^ n) (div_pos hT (by positivity))) := by
  have := kernelProfileMeasure_probability Φ hΦ
  have hs : T / 2 ^ n ≤ 1 :=
    (div_le_one (by positivity : (0 : ℝ) < 2 ^ n)).2
      (hT1.trans (one_le_pow₀ (by norm_num)))
  have := infiniteKernelMeasure_probability Φ hΦ hT hT1
  have := infiniteKernelMeasure_probability Φ hΦ (div_pos hT (by positivity)) hs
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [integral_infiniteKernelMeasure Φ hΦ hT hT1,
    infiniteKernel_block Φ hΦ hT hT1 n]
  have hk := (infiniteKernel Φ hΦ (T / 2 ^ n) (div_pos hT (by positivity))).continuous.integrable_of_hasCompactSupport (μ := volume)
      (infiniteKernel_hasCompactSupport Φ hΦ (div_pos hT (by positivity)) hs)
  rw [integral_probabilityConvolution_mul _ _ _ hk, integral_conv (g.integrable _)]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  dsimp only
  rw [integral_infiniteKernelMeasure Φ hΦ (div_pos hT (by positivity)) hs]
  simp only [add_comm y]

/-- The one-step measure factorisation. -/
theorem infiniteKernelMeasure_recursion (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    infiniteKernelMeasure Φ hΦ T hT =
      (dyadicKernelFactor (kernelProfileMeasure Φ) T 0).conv
        (infiniteKernelMeasure Φ hΦ (T / 2) (half_pos hT)) := by
  have := kernelProfileMeasure_probability Φ hΦ
  simpa only [pow_one, dyadicKernelMeasure_one] using
    infiniteKernelMeasure_block Φ hΦ hT hT1 1

end GlobalPhi43.MW20
