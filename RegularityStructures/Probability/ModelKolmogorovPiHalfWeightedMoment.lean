/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.BlockEnvelope.Moment
public import RegularityStructures.Probability.SpaceTimeMeasure
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Weighted block-envelope moments

If the pointwise `p`-th moment of a random field `Y ω w` is bounded by
`(c * |x - w|^α)^p`, then the `p`-th moment of its block-envelope average around `x`
is bounded by `(M c s^(α/4))^p`.  This is the weighted version of
`exists_kernelBlockEnvelope_lintegral_pow_moment_le` and is the moment engine of PH-A.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

private instance parabolicSpaceVolumeIsAddHaarPiHalfWeighted :
    (volume : Measure ParabolicSpace).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

private instance parabolicSpaceVolumeIsNegInvariantPiHalfWeighted :
    (volume : Measure ParabolicSpace).IsNegInvariant := by
  exact ⟨((Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (Measure.measurePreserving_neg (volume : Measure (Fin 3 → ℝ)))).map_eq⟩

theorem piHalfJensen
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {k y : α → ℝ≥0∞} {p : ℕ} (hp : 1 ≤ p)
    (hk : AEMeasurable k μ) (hy : AEMeasurable y μ) :
    (∫⁻ z, k z * y z ∂μ) ^ p ≤
      (∫⁻ z, k z ∂μ) ^ (p - 1) * ∫⁻ z, k z * (y z) ^ p ∂μ := by
  by_cases hp1 : p = 1
  · subst p
    simp
  have hp2 : 2 ≤ p := by omega
  have hp0 : p ≠ 0 := by omega
  let q₁ : ℝ := 1 - 1 / (p : ℝ)
  let q₂ : ℝ := 1 / (p : ℝ)
  have hpcast : (1 : ℝ) < p := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hp2)
  have hppos : (0 : ℝ) < p := by linarith
  have hq₂pos : 0 < q₂ := by
    dsimp [q₂]
    exact one_div_pos.mpr hppos
  have hq₂lt : q₂ < 1 := by
    dsimp [q₂]
    rw [div_lt_iff₀ hppos]
    simpa using hpcast
  have hq₁pos : 0 < q₁ := by
    dsimp [q₁]
    exact sub_pos.mpr hq₂lt
  have hq₁ : 0 ≤ q₁ := hq₁pos.le
  have hq₂ : 0 ≤ q₂ := by
    dsimp [q₂]
    positivity
  have hqsum : q₁ + q₂ = 1 := by
    dsimp [q₁, q₂]
    ring
  have hprod : AEMeasurable (fun z => k z * (y z) ^ p) μ :=
    hk.mul (hy.pow_const p)
  have hj := ENNReal.lintegral_mul_norm_pow_le
    (μ := μ) (f := k) (g := fun z => k z * (y z) ^ p)
    hk hprod hq₁ hq₂ hqsum
  have hpoint : ∀ z, k z ^ q₁ * (k z * y z ^ p) ^ q₂ = k z * y z := by
    intro z
    by_cases hk0 : k z = 0
    · simp [hk0, hq₁pos, hq₂pos]
    by_cases hktop : k z = ⊤
    · by_cases hy0 : y z = 0
      · simp [hktop, hy0, hp0, hq₁pos, hq₂pos]
      · simp [hktop, hy0, ENNReal.top_rpow_of_pos hq₁pos,
          ENNReal.top_rpow_of_pos hq₂pos,
          ENNReal.top_mul (pow_ne_zero _ hy0)]
    · rw [ENNReal.mul_rpow_of_nonneg _ _ hq₂]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← mul_assoc,
        ← ENNReal.rpow_add q₁ q₂ hk0 hktop, hqsum, ENNReal.rpow_one]
      rw [show (p : ℝ) * q₂ = 1 by
        dsimp [q₂]
        field_simp]
      simp
  rw [← ENNReal.rpow_natCast]
  have hj' := ENNReal.rpow_le_rpow hj (by positivity : 0 ≤ (p : ℝ))
  rw [show (fun z => k z ^ q₁ * (k z * y z ^ p) ^ q₂) =
      (fun z => k z * y z) by funext z; exact hpoint z] at hj'
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (p : ℝ))] at hj'
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hj'
  have hq₁p : q₁ * (p : ℝ) = (p - 1 : ℕ) := by
    dsimp [q₁]
    rw [Nat.cast_sub (by omega)]
    field_simp
    norm_num
  have hq₂p : q₂ * (p : ℝ) = 1 := by
    dsimp [q₂]
    field_simp
  rw [hq₁p, hq₂p, ENNReal.rpow_one] at hj'
  simpa only [ENNReal.rpow_natCast] using hj'

theorem measurable_kernelBlockEnvelope_shift (n : ℕ) {s : ℝ} (hs : 0 < s) (x : ParabolicSpace) :
    Measurable (fun w => kernelBlockEnvelope n s (x - w)) := by
  have henv : Measurable (kernelBlockEnvelope n s) := by
    rw [funext (kernelBlockEnvelope_eq_envelopeWeight n hs)]
    exact measurable_envelopeWeight _ _ _
  exact henv.comp (measurable_const.sub measurable_id)

/-- The envelope moments in `lintegral` form, centred at an arbitrary point `x`. -/
theorem exists_lintegral_kernelBlockEnvelope_shift_mul_rpow_le {n : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hn : a + 1 < n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {s : ℝ}, 0 < s → ∀ x : ParabolicSpace,
      ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) *
          ENNReal.ofReal (parabolicNorm (x - w) ^ a) ≤ ENNReal.ofReal (M * s ^ (a / 4)) := by
  obtain ⟨M, hM, hmoment⟩ := exists_integral_kernelBlockEnvelope_mul_rpow_le ha hn
  refine ⟨M, hM, fun {s} hs x => ?_⟩
  have hmp := volume.measurePreserving_sub_left x
  have hF : Integrable (fun z => kernelBlockEnvelope n s z * parabolicNorm z ^ a) :=
    integrable_kernelBlockEnvelope_mul_rpow ha hn hs
  have hFcomp : Integrable (fun w => kernelBlockEnvelope n s (x - w) *
      parabolicNorm (x - w) ^ a) := by
    simpa [Function.comp_def] using hmp.integrable_comp_of_integrable hF
  have hnn : ∀ w, 0 ≤ kernelBlockEnvelope n s (x - w) * parabolicNorm (x - w) ^ a := fun w =>
    mul_nonneg (kernelBlockEnvelope_nonneg n hs _)
      (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
  have hpt : ∀ w, ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) *
        ENNReal.ofReal (parabolicNorm (x - w) ^ a) =
      ENNReal.ofReal (kernelBlockEnvelope n s (x - w) * parabolicNorm (x - w) ^ a) := fun w =>
    (ENNReal.ofReal_mul (kernelBlockEnvelope_nonneg n hs _)).symm
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hFcomp (Filter.Eventually.of_forall hnn)]
  refine ENNReal.ofReal_le_ofReal ?_
  have htrans : ∫ w, kernelBlockEnvelope n s (x - w) * parabolicNorm (x - w) ^ a =
      ∫ z, kernelBlockEnvelope n s z * parabolicNorm z ^ a :=
    hmp.integral_comp (measurableEmbedding_subLeft x)
      (fun z => kernelBlockEnvelope n s z * parabolicNorm z ^ a)
  rw [htrans]
  exact hmoment s hs

end RegularityStructures

end
