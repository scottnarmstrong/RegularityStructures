/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.Growth

/-!
# Chebyshev bounds with a finite variance bound

The real and imaginary parts of a Fourier mode on a finite time window need not have unit
`L²` norm.  This module records the corresponding form of the Gaussian growth estimate.  The
variance bound is deliberately an explicit hypothesis, so the result can also be reused for
other finite-variance Gaussian coordinate families.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem whiteNoise_measure_abs_gt_le_chebyshev_of_integral_sq_le
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {e : ι → SpaceTime → ℝ} (he : ∀ i, MemLp (e i) 2)
    {V : ℝ} (hvariance : ∀ i, ∫ z, e i z * e i z ≤ V)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) :
    ∀ i, P {ω | b i < |W (e i) ω|} ≤
      ENNReal.ofReal ((b i)⁻¹ ^ 2 * V) := by
  intro i
  have hcent := hW.2 1 (fun _ => e i) (fun _ => he i)
  have hcoord : MemLp (fun ω => W (e i) ω) 2 P := hcent.memLp_two_apply 0
  have hbound := measure_abs_gt_le_integral_sq_div P hcoord (hb i)
  have hsq : ∫ ω, (W (e i) ω) ^ (2 : ℕ) ∂P = ∫ z, e i z * e i z := by
    calc
      ∫ ω, (W (e i) ω) ^ (2 : ℕ) ∂P =
          ∫ ω, W (e i) ω * W (e i) ω ∂P := by simp [pow_two]
      _ = ∫ z, e i z * e i z := hcent.integral_mul 0 0
  rw [hsq] at hbound
  calc
    P {ω | b i < |W (e i) ω|} ≤
        ENNReal.ofReal ((b i)⁻¹ ^ 2 * ∫ z, e i z * e i z) := hbound
    _ ≤ ENNReal.ofReal ((b i)⁻¹ ^ 2 * V) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (hvariance i) (sq_nonneg _)

theorem whiteNoise_ae_eventually_bound_of_integral_sq_le
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Countable ι] {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {e : ι → SpaceTime → ℝ} (he : ∀ i, MemLp (e i) 2)
    {V : ℝ} (hvariance : ∀ i, ∫ z, e i z * e i z ≤ V)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (hsum : (∑' i, ENNReal.ofReal ((b i)⁻¹ ^ 2 * V)) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ᶠ i in (Filter.cofinite : Filter ι), |W (e i) ω| ≤ b i := by
  apply ae_eventually_le_of_summable_chebyshev P
  · exact whiteNoise_measure_abs_gt_le_chebyshev_of_integral_sq_le hW he hvariance b hb
  · exact hsum

end RegularityStructures.Phi43

end
