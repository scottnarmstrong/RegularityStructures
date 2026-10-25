/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceNoisePairProduct
public import Phi43.Stochastic.StochasticHeatConvergenceDeterministicPair
import Phi43.Stochastic.StochasticHeatConvergencePathwiseNoise

/-!
# The second moment of the pathwise stationary convolution

For an arbitrary regularised-noise version the pathwise massive heat convolution is in L²
and has the variance of the canonical white-noise pairing. The stochastic and deterministic
covariance Fubini hypotheses have already been proved, rather than added to the statement.

Source: the statement, equation (2.2) and Definition 2.5.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

private theorem convolution_square_eq_pair
    {Ω : Type*} (ξ : Ω → SpaceTime → ℝ) (ω : Ω) (z : SpaceTime) :
    (∫ w : SpaceTime, massiveHeatKernel (z - w) * ξ ω w) ^ 2 =
      ∫ q : SpaceTime × SpaceTime,
        massiveHeatKernel (z - q.1) * massiveHeatKernel (z - q.2) * ξ ω q.1 * ξ ω q.2
        ∂((volume : Measure SpaceTime).prod volume) := by
  rw [pow_two, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  ring

theorem regularisedNoise_massiveHeatKernel_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    MemLp (fun ω => ∫ w : SpaceTime, massiveHeatKernel (z - w) * ξ ω w) 2 P := by
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hAm : Measurable (fun ω => ∫ w : SpaceTime, massiveHeatKernel (z - w) * ξ ω w) :=
    (regularisedNoise_massiveHeatKernel_convolution_measurable ρ ξ hξ).comp
      (measurable_id.prodMk measurable_const)
  apply (memLp_two_iff_integrable_sq hAm.aestronglyMeasurable).mpr
  have hi := regularisedNoise_massiveHeatKernel_pair_product_integrable hW ρ hρ hε ξ hξ z
  apply hi.integral_prod_left.congr
  exact Filter.Eventually.of_forall fun ω => (convolution_square_eq_pair ξ ω z).symm

theorem regularisedNoise_massiveHeatKernel_second_moment_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    (∫ ω, (∫ w : SpaceTime, massiveHeatKernel (z - w) * ξ ω w) ^ 2 ∂P) =
      ∫ v : SpaceTime, mollifiedKernel ρ ε (z - v) ^ 2 := by
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let H : Ω × (SpaceTime × SpaceTime) → ℝ := fun q =>
    massiveHeatKernel (z - q.2.1) * massiveHeatKernel (z - q.2.2) * ξ q.1 q.2.1 * ξ q.1 q.2.2
  have hHi : Integrable H (P.prod ((volume : Measure SpaceTime).prod volume)) :=
    regularisedNoise_massiveHeatKernel_pair_product_integrable hW ρ hρ hε ξ hξ z
  have hin (q : SpaceTime × SpaceTime) :
      (∫ ω, H (ω, q) ∂P) = massiveHeatKernel (z - q.1) * massiveHeatKernel (z - q.2) *
        ∫ v : SpaceTime, mollifierAt ρ ε q.1 v * mollifierAt ρ ε q.2 v := by
    rw [← regularisedNoise_pair_integral hW ρ hρ hε ξ hξ q.1 q.2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp [H]
    ring
  have hcov : Integrable (fun q : SpaceTime × SpaceTime =>
      massiveHeatKernel (z - q.1) * massiveHeatKernel (z - q.2) *
        ∫ v : SpaceTime, mollifierAt ρ ε q.1 v * mollifierAt ρ ε q.2 v)
      ((volume : Measure SpaceTime).prod volume) := by
    apply hHi.integral_prod_right.congr
    exact Filter.Eventually.of_forall hin
  calc
    _ = ∫ ω, ∫ q : SpaceTime × SpaceTime, H (ω, q)
        ∂((volume : Measure SpaceTime).prod volume) ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => convolution_square_eq_pair ξ ω z
    _ = ∫ q : SpaceTime × SpaceTime, (∫ ω, H (ω, q) ∂P)
        ∂((volume : Measure SpaceTime).prod volume) := integral_integral_swap hHi
    _ = ∫ x : SpaceTime, ∫ y : SpaceTime,
        massiveHeatKernel (z - x) * massiveHeatKernel (z - y) *
          ∫ v : SpaceTime, mollifierAt ρ ε x v * mollifierAt ρ ε y v := by
      simp_rw [hin]
      exact integral_prod _ hcov
    _ = _ := integral_massive_mollifierAt_covariance_pair_eq ρ hρ hε z

end RegularityStructures.Phi43

end
