/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceNoisePair

/-!
# Integrability of stochastic covariance Fubini

The product of two massive-kernel-weighted forcing evaluations is integrable jointly in the
sample and both space-time points. All Fubini hypotheses follow from the uniform pointwise
second moment and the L¹ massive kernel; none is assumed as a new stochastic input.

Source: the statement, equation (2.2) and Definition 2.4.
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

theorem regularisedNoise_massiveHeatKernel_pair_product_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    Integrable (fun q : Ω × (SpaceTime × SpaceTime) =>
      massiveHeatKernel (z - q.2.1) * massiveHeatKernel (z - q.2.2) *
        ξ q.1 q.2.1 * ξ q.1 q.2.2)
      (P.prod ((volume : Measure SpaceTime).prod volume)) := by
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let φ : SpaceTime → ℝ := fun x => massiveHeatKernel (z - x)
  let V : ℝ := ∫ v : SpaceTime, periodise ρ ε v ^ 2
  have hφm : Measurable φ := measurable_massiveHeatKernel.comp (measurable_const.sub measurable_id)
  have hφi : Integrable φ := integrable_comp_sub_left_spaceTime integrable_massiveHeatKernel z
  have hξm := regularisedNoise_measurable_uncurry P W ρ ε ξ hξ
  let H : (SpaceTime × SpaceTime) × Ω → ℝ := fun q =>
    (φ q.1.1 * φ q.1.2) * (ξ q.2 q.1.1 * ξ q.2 q.1.2)
  have hHm : Measurable H :=
    ((hφm.comp (measurable_fst.comp measurable_fst)).mul
      (hφm.comp (measurable_snd.comp measurable_fst))).mul
      ((hξm.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).mul
        (hξm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hinner (q : SpaceTime × SpaceTime) : Integrable (fun ω => H (q, ω)) P := by
    have hi := ((regularisedNoise_memLp_two hW ρ hρ hε ξ hξ q.1).integrable_mul
      (regularisedNoise_memLp_two hW ρ hρ hε ξ hξ q.2)).const_mul (φ q.1 * φ q.2)
    simpa only [H, Pi.mul_apply] using hi
  have hHi : Integrable H (((volume : Measure SpaceTime).prod volume).prod P) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hinner, ?_⟩
    apply ((hφi.norm.mul_prod hφi.norm).mul_const V).mono'
      hHm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [] with q
    rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
    calc
      (∫ ω, ‖H (q, ω)‖ ∂P) =
          (‖φ q.1‖ * ‖φ q.2‖) * ∫ ω, |ξ ω q.1 * ξ ω q.2| ∂P := by
        simp only [H, norm_mul, Real.norm_eq_abs, abs_mul]
        exact integral_const_mul _ _
      _ ≤ (‖φ q.1‖ * ‖φ q.2‖) * V :=
        mul_le_mul_of_nonneg_left
          (regularisedNoise_pair_abs_integral_le_periodise_sq hW ρ hρ hε ξ hξ q.1 q.2)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply hHi.swap.congr
  filter_upwards [] with q
  dsimp [H, φ]
  ring

end RegularityStructures.Phi43

end
