/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.WhiteNoise
public import RegularityStructures.Probability.GaussianVector
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Polynomial growth of Gaussian coordinates

The first Borel–Cantelli lemma turns the summable Chebyshev estimates for the coordinates of a
Gaussian family into an almost-sure eventual polynomial bound.  The probabilistic estimate is
kept as an explicit hypothesis: this makes the result applicable both to standard Gaussian
coordinates and to coordinates obtained from an arbitrary white noise.  The estimate is exactly
the one obtained from Chebyshev's inequality, `P (|Z i| > b i) ≤ (b i)⁻²` for unit-variance
coordinates.  This is the countable-coordinate input used in the Fourier series construction.

The use of the cofinite filter is intentional.  A finite exceptional set is harmless for a smooth
series, while requiring a deterministic bound at every coordinate would be false for Gaussian
families.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem ae_eventually_le_of_summable_chebyshev
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (P : Measure Ω)
    {X : ι → Ω → ℝ} {b : ι → ℝ} {q : ι → ℝ≥0∞}
    (hprob : ∀ i, P {ω | b i < |X i ω|} ≤ q i)
    (hsum : (∑' i, q i) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ᶠ i in (Filter.cofinite : Filter ι), |X i ω| ≤ b i := by
  have hsum' : (∑' i, P {ω | b i < |X i ω|}) ≠ ∞ := by
    exact ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hprob)
  have hbc := ae_finite_setOfPred_mem (μ := P)
    (s := fun i : ι => {ω | b i < |X i ω|}) hsum'
  filter_upwards [hbc] with ω hω
  filter_upwards [hω.eventually_cofinite_notMem] with i hi
  exact not_lt.mp hi

theorem measure_abs_gt_le_integral_sq_div
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) {b : ℝ} (hb : 0 < b) :
    P {ω | b < |X ω|} ≤
      ENNReal.ofReal (b⁻¹ ^ 2 * ∫ ω, (X ω) ^ 2 ∂P) := by
  have hXsq : Integrable (fun ω => (X ω) ^ 2) P := by
    simpa [Real.norm_eq_abs] using hX.integrable_norm_pow' (p := 2)
  have hscaled : Integrable (fun ω => (X ω / b) ^ 2) P := by
    have hmul := hXsq.const_mul (b⁻¹ ^ 2)
    convert hmul using 1
    · funext ω
      field_simp [ne_of_gt hb]
  have hnonneg : 0 ≤ᵐ[P] (fun ω => (X ω / b) ^ 2) :=
    ae_of_all _ fun ω => sq_nonneg _
  have hone : ∀ ω ∈ {ω | b < |X ω|}, 1 ≤ (X ω / b) ^ 2 := by
    intro ω hω
    apply (one_le_sq_iff_one_le_abs _).2
    rw [abs_div, abs_of_pos hb]
    exact (one_le_div hb).2 (le_of_lt hω)
  have hmeasure := hscaled.measure_le_integral hnonneg hone
  have hintegral :
      (∫ ω, (X ω / b) ^ 2 ∂P) = b⁻¹ ^ 2 * ∫ ω, (X ω) ^ 2 ∂P := by
    calc
      (∫ ω, (X ω / b) ^ 2 ∂P) =
          ∫ ω, b⁻¹ ^ 2 * (X ω) ^ 2 ∂P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            field_simp [ne_of_gt hb]
      _ = b⁻¹ ^ 2 * ∫ ω, (X ω) ^ 2 ∂P := integral_const_mul _ _
  rw [hintegral] at hmeasure
  exact hmeasure

end RegularityStructures.Phi43

end
