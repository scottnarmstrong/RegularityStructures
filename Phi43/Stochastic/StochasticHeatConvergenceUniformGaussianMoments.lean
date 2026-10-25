/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceUniformSize
public import Phi43.Stochastic.StochasticHeatConvergenceMoments

/-!
# Uniform even Gaussian moments for the size and time-increment bounds

The unconditional kernel estimates give all even moments by the centred Gaussian moment
formula. Constants are chosen before the noise, mollification, heat and space-time variables.
These estimates provide the arbitrarily high moments used by Kolmogorov--Chentsov.
-/

@[expose] public noncomputable section

open MeasureTheory Real ProbabilityTheory

namespace RegularityStructures.Phi43

theorem stochasticHeatField_even_moment_bound_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε s : ℝ}, 0 < ε → ε ≤ 1 → 0 < s → s ≤ 1 → ∀ z : SpaceTime,
      (∫ ω, |stochasticHeatField W ρ ε s z ω| ^ (2 * m) ∂P) ≤
        C * s ^ (-((m : ℝ) / 2)) := by
  obtain ⟨C₀, hC₀, hbound⟩ := stochasticHeatKernel_sq_bound_uniform ρ hρ
  let M : ℝ := ∫ u : ℝ, |u| ^ (2 * m) ∂gaussianReal 0 1
  have hM : 0 ≤ M := integral_nonneg fun u => pow_nonneg (abs_nonneg _) _
  refine ⟨M * C₀ ^ m, mul_nonneg hM (pow_nonneg hC₀ _), ?_⟩
  intro Ω _ P W hW ε s hε hε1 hs hs1 z
  have hm : MemLp (stochasticHeatKernel ρ ε s z) 2 :=
    memLp_stochasticHeatKernel_of_integrable_square ρ hρ hε hs z
      (integrable_stochasticHeatKernel_square_of_mollifiedKernel_facts ρ hρ hε hs z)
  have hmoment := stochasticHeat_pairing_even_abs_moment_le hW hm
    (hbound hε hε1 hs hs1 z) m
  have hpow : (s ^ (-(1 / 2 : ℝ))) ^ m = s ^ (-((m : ℝ) / 2)) := by
    rw [← rpow_natCast, ← rpow_mul hs.le]
    congr 1
    ring
  simpa only [stochasticHeatField, mul_pow, hpow, mul_assoc, M] using hmoment

theorem stochasticHeatField_time_increment_even_moment_bound_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε s : ℝ}, 0 < ε → ε ≤ 1 → 0 < s → s ≤ 1 →
      ∀ t t' : ℝ, ∀ x : Torus3,
      (∫ ω, |stochasticHeatField W ρ ε s (t, x) ω -
        stochasticHeatField W ρ ε s (t', x) ω| ^ (2 * m) ∂P) ≤
        C * |t - t'| ^ ((m : ℝ) * θ) *
          s ^ (-((m : ℝ) / 2 + (m : ℝ) * θ)) := by
  obtain ⟨C₀, hC₀, hbound⟩ := stochasticHeatKernel_time_increment_sq_bound_uniform ρ hρ hθ hθ1
  let M : ℝ := ∫ u : ℝ, |u| ^ (2 * m) ∂gaussianReal 0 1
  have hM : 0 ≤ M := integral_nonneg fun u => pow_nonneg (abs_nonneg _) _
  refine ⟨M * C₀ ^ m, mul_nonneg hM (pow_nonneg hC₀ _), ?_⟩
  intro Ω _ P W hW ε s hε hε1 hs hs1 t t' x
  have hm (z : SpaceTime) : MemLp (stochasticHeatKernel ρ ε s z) 2 :=
    memLp_stochasticHeatKernel_of_integrable_square ρ hρ hε hs z
      (integrable_stochasticHeatKernel_square_of_mollifiedKernel_facts ρ hρ hε hs z)
  have hmoment := stochasticHeat_pairing_even_abs_moment_le hW
    ((hm (t, x)).sub (hm (t', x))) (hbound hε hε1 hs hs1 t t' x) m
  have hleft :
      (∫ ω, |stochasticHeatField W ρ ε s (t, x) ω -
          stochasticHeatField W ρ ε s (t', x) ω| ^ (2 * m) ∂P) =
        ∫ ω, |W (stochasticHeatKernel ρ ε s (t, x) -
          stochasticHeatKernel ρ ε s (t', x)) ω| ^ (2 * m) ∂P := by
    apply integral_congr_ae
    filter_upwards [whiteNoise_pairing_sub_ae hW (hm (t, x)) (hm (t', x))] with ω hω
    exact congrArg (fun a : ℝ => |a| ^ (2 * m)) hω
  have htime : (|t - t'| ^ θ) ^ m = |t - t'| ^ ((m : ℝ) * θ) := by
    rw [← rpow_natCast, ← rpow_mul (abs_nonneg _)]
    congr 1
    ring
  have hscale : (s ^ (-(1 / 2 + θ : ℝ))) ^ m =
      s ^ (-((m : ℝ) / 2 + (m : ℝ) * θ)) := by
    rw [← rpow_natCast, ← rpow_mul hs.le]
    congr 1
    ring
  rw [hleft]
  simpa only [mul_pow, htime, hscale, mul_assoc, M] using hmoment

end RegularityStructures.Phi43

end
