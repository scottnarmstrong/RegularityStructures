module

public import GlobalPhi43.MW20.DyadicConvolutionLimit
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The actual smooth probability profile used by MW20

The support condition is the source past unit ball for the max parabolic
metric, not the sum-type parabolic size used in some RS test classes.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set
open scoped ContDiff ENNReal

/-- The source past unit ball. -/
@[expose] def kernelPastUnitBall : Set ParabolicSpace :=
  {z | -1 < z.1 ∧ z.1 < 0 ∧ ∀ i, |z.2 i| < 1}

/-- Exactly the source assumptions on the seed profile Φ. -/
structure KernelProfile (Φ : ParabolicSpace → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ Φ
  compact : HasCompactSupport Φ
  support : tsupport Φ ⊆ kernelPastUnitBall
  nonneg : ∀ z, 0 ≤ Φ z
  le_one : ∀ z, Φ z ≤ 1
  mass : ∫ z, Φ z = 1
  spatial_even : ∀ t x, Φ (t, -x) = Φ (t, x)

/-- The actual probability measure with density Φ. -/
@[expose] noncomputable def kernelProfileMeasure (Φ : ParabolicSpace → ℝ) : Measure ParabolicSpace :=
  volume.withDensity (fun z => ENNReal.ofReal (Φ z))

/-- Smooth compact profiles with unit integral give probability measures. -/
theorem kernelProfileMeasure_probability (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    IsProbabilityMeasure (kernelProfileMeasure Φ) := by
  constructor
  rw [kernelProfileMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (hΦ.smooth.continuous.integrable_of_hasCompactSupport hΦ.compact)
      (ae_of_all volume hΦ.nonneg), hΦ.mass]
  norm_num

/-- The source support implies ordinary norm at most one. -/
theorem norm_le_one_of_mem_kernelPastUnitBall {z : ParabolicSpace} (hz : z ∈ kernelPastUnitBall) :
    ‖z‖ ≤ 1 := by
  rw [Prod.norm_def]
  apply max_le
  · rw [Real.norm_eq_abs, abs_le]
    exact ⟨hz.1.le, hz.2.1.le.trans (by norm_num)⟩
  · exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 (fun i => (hz.2.2 i).le)

/-- The support radius needed for convergence is derived from the actual density. -/
theorem kernelProfileMeasure_ae_norm_le (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∀ᵐ z ∂kernelProfileMeasure Φ, ‖z‖ ≤ 1 := by
  unfold kernelProfileMeasure
  apply (ae_withDensity_iff (hΦ.smooth.continuous.measurable.ennreal_ofReal)).2
  apply ae_of_all
  intro z hz
  have hne : Φ z ≠ 0 := by
    intro he
    simp [he] at hz
  exact norm_le_one_of_mem_kernelPastUnitBall
    (hΦ.support (subset_tsupport Φ (Function.mem_support.mpr hne)))

end GlobalPhi43.MW20
