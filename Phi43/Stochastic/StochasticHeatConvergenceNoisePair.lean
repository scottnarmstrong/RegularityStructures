/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceNoiseMoments
import Phi43.Stochastic.WhiteNoiseCovariance

/-!
# Covariance and absolute-product bounds for arbitrary regularised-noise versions

Pointwise almost-sure identification with white noise gives the covariance identity without
requiring a jointly measurable canonical family. The uniform absolute-product estimate is the
dominating bound for version-safe stochastic Fubini.

Source: the statement, Definition 2.4 and the white-noise covariance specification.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem regularisedNoise_pair_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) (z z' : SpaceTime) :
    (∫ ω, ξ ω z * ξ ω z' ∂P) =
      ∫ v : SpaceTime, mollifierAt ρ ε z v * mollifierAt ρ ε z' v := by
  calc
    _ = ∫ ω, W (mollifierAt ρ ε z) ω * W (mollifierAt ρ ε z') ω ∂P := by
      apply integral_congr_ae
      filter_upwards [(hξ.2 z).2, (hξ.2 z').2] with ω hω hω'
      rw [hω, hω']
    _ = _ := whiteNoise_pairing_mul_integral hW
      (memLp_mollifierAt ρ hρ hε z) (memLp_mollifierAt ρ hρ hε z')

private theorem abs_mul_le_half_sum_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith only [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

theorem regularisedNoise_pair_abs_integral_le_periodise_sq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) (z z' : SpaceTime) :
    (∫ ω, |ξ ω z * ξ ω z'| ∂P) ≤ ∫ v : SpaceTime, periodise ρ ε v ^ 2 := by
  have hL := regularisedNoise_memLp_two hW ρ hρ hε ξ hξ z
  have hR := regularisedNoise_memLp_two hW ρ hρ hε ξ hξ z'
  have hprod : Integrable (fun ω => ξ ω z * ξ ω z') P := hL.integrable_mul hR
  calc
    _ ≤ ∫ ω, (ξ ω z ^ 2 + ξ ω z' ^ 2) / 2 ∂P :=
      integral_mono hprod.norm ((hL.integrable_sq.add hR.integrable_sq).div_const 2)
        (fun ω => abs_mul_le_half_sum_sq _ _)
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, integral_add hL.integrable_sq hR.integrable_sq,
        regularisedNoise_second_moment_eq_periodise_sq hW ρ hρ hε ξ hξ z,
        regularisedNoise_second_moment_eq_periodise_sq hW ρ hρ hε ξ hξ z']
      ring

end RegularityStructures.Phi43

end
