/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonDefinitions
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The reduction for the comparison of the constants

This file formalises the reduction in Section 7 of the statement.  The first reduction is
the `L⁴ × L^(4/3)` pairing used for (10.33); the second is dominated convergence applied to the
two terms in the difference of (10.41).  The records below contain only analytic estimates, not
an alternative definition of either constant.  Consequently, an eventual construction of the
periodised Hairer-kernel estimates can be plugged into these theorems without changing the
constants.

The record `ConstantsComparisonC2Data` isolates the analytic steps. The module
`Phi43.Stochastic.ConstantsComparisonSunset` constructs its fields from the actual causal kernels
and `IsMollifier ρ`, and `Phi43.Stochastic.ConstantsComparisonLimits` states the comparison with
no further hypotheses.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.Phi43

/-- The real-valued `Lᵖ` quantity used in the Section 7 Hölder calculation. -/
def constantsComparisonLpNorm (f : SpaceTime → ℝ) (p : ℝ) : ℝ :=
  (∫ z, ‖f z‖ ^ p) ^ (1 / p)

/-- The dominated-convergence inputs for the two terms in the second-constant comparison. -/
structure ConstantsComparisonC2Data (N : ℕ)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) where
  covariance_limit : SpaceTime → ℝ
  hairer_covariance_limit : SpaceTime → ℝ
  covariance_tendsto : ∀ᵐ z ∂volume, Tendsto (fun ε : ℝ => covariance ρ ε z)
    (𝓝[>] 0) (𝓝 (covariance_limit z))
  hairer_covariance_tendsto : ∀ᵐ z ∂volume,
    Tendsto (fun ε : ℝ => hairerCovariance N ρ ε z)
      (𝓝[>] 0) (𝓝 (hairer_covariance_limit z))
  massive_integrable : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    Integrable (fun z : SpaceTime => massiveHeatKernel z * covariance ρ ε z ^ 2)
  hairer_integrable : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    Integrable (fun z : SpaceTime => hairerKernelTorus N z *
      hairerCovariance N ρ ε z ^ 2)
  remainder_integrable : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    Integrable (fun z : SpaceTime => constantsComparisonR N z * covariance ρ ε z ^ 2)
  correction_integrable : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    Integrable (fun z : SpaceTime => hairerKernelTorus N z *
      (covariance ρ ε z - hairerCovariance N ρ ε z) *
      (covariance ρ ε z + hairerCovariance N ρ ε z))
  first_measurable : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    AEStronglyMeasurable (fun z : SpaceTime =>
      constantsComparisonR N z * covariance ρ ε z ^ 2) volume
  second_measurable : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    AEStronglyMeasurable (fun z : SpaceTime =>
      hairerKernelTorus N z *
        (covariance ρ ε z - hairerCovariance N ρ ε z) *
        (covariance ρ ε z + hairerCovariance N ρ ε z)) volume
  first_bound : ∃ d : SpaceTime → ℝ, Integrable d ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    ∀ᵐ z ∂volume, ‖constantsComparisonR N z * covariance ρ ε z ^ 2‖ ≤ d z
  second_bound : ∃ d : SpaceTime → ℝ, Integrable d ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    ∀ᵐ z ∂volume, ‖hairerKernelTorus N z *
        (covariance ρ ε z - hairerCovariance N ρ ε z) *
        (covariance ρ ε z + hairerCovariance N ρ ε z)‖ ≤ d z

theorem constantsComparison_sunset_tendsto (N : ℕ)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (h : ConstantsComparisonC2Data N ρ) :
    Tendsto
      (fun ε : ℝ => sunsetConstant ρ ε - hairerSunsetConstant N ρ ε)
      (𝓝[>] 0)
      (𝓝 (2 * (∫ z, constantsComparisonR N z * h.covariance_limit z ^ 2) +
        2 * (∫ z, hairerKernelTorus N z *
          (h.covariance_limit z - h.hairer_covariance_limit z) *
          (h.covariance_limit z + h.hairer_covariance_limit z)))) := by
  obtain ⟨d₁, hd₁, hdom₁⟩ := h.first_bound
  obtain ⟨d₂, hd₂, hdom₂⟩ := h.second_bound
  let l : Filter ℝ := 𝓝[>] 0
  have hpos : ∀ᶠ ε in l, 0 < ε := self_mem_nhdsWithin
  have hle : ∀ᶠ ε in l, ε ≤ 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  have hfirst : Tendsto
      (fun ε : ℝ => 2 * ∫ z, constantsComparisonR N z * covariance ρ ε z ^ 2)
      l (𝓝 (2 * ∫ z, constantsComparisonR N z * h.covariance_limit z ^ 2)) := by
    apply Tendsto.const_mul
    refine tendsto_integral_filter_of_dominated_convergence d₁ ?_ ?_ hd₁ ?_
    · filter_upwards [hpos, hle] with ε hε hε1
      exact (h.first_measurable hε hε1)
    · filter_upwards [hpos, hle] with ε hε hε1
      exact hdom₁ hε hε1
    · filter_upwards [h.covariance_tendsto] with z hz
      simpa only [one_mul] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) l (𝓝 1)).mul
          (hz.pow 2)).const_mul (constantsComparisonR N z)
  have hsecond : Tendsto
      (fun ε : ℝ => 2 * ∫ z, hairerKernelTorus N z *
        (covariance ρ ε z - hairerCovariance N ρ ε z) *
        (covariance ρ ε z + hairerCovariance N ρ ε z)) l
      (𝓝 (2 * ∫ z, hairerKernelTorus N z *
        (h.covariance_limit z - h.hairer_covariance_limit z) *
        (h.covariance_limit z + h.hairer_covariance_limit z))) := by
    apply Tendsto.const_mul
    refine tendsto_integral_filter_of_dominated_convergence d₂ ?_ ?_ hd₂ ?_
    · filter_upwards [hpos, hle] with ε hε hε1
      exact h.second_measurable hε hε1
    · filter_upwards [hpos, hle] with ε hε hε1
      exact hdom₂ hε hε1
    · filter_upwards [h.covariance_tendsto, h.hairer_covariance_tendsto] with z hg hk
      have hminus := hg.sub hk
      have hplus := hg.add hk
      simpa only [one_mul, mul_assoc] using
        (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) l (𝓝 1)).mul hminus).mul
          hplus).const_mul (hairerKernelTorus N z)
  have hsum := hfirst.add hsecond
  refine hsum.congr' ?_
  filter_upwards [hpos, hle] with ε hε hε1
  exact (sunsetConstant_sub_hairerSunsetConstant_integrand N ρ ε
    (h.massive_integrable hε hε1) (h.hairer_integrable hε hε1)
    (h.remainder_integrable hε hε1) (h.correction_integrable hε hε1)).symm

/-- The Section 7 constant `κ`, once the two comparison limits are supplied. -/
def constantsComparisonKappa (c₁ c₂ : ℝ) : ℝ := 3 * c₁ - 9 * c₂

theorem constantsComparison_counterterm_tendsto
    {N : ℕ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : Tendsto (fun ε : ℝ => wickConstant ρ ε - hairerWickConstant N ρ ε)
      (𝓝[>] 0) (𝓝 L₁))
    (h₂ : Tendsto (fun ε : ℝ => sunsetConstant ρ ε - hairerSunsetConstant N ρ ε)
      (𝓝[>] 0) (𝓝 L₂)) :
    Tendsto
      (fun ε : ℝ => 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε -
        (3 * hairerWickConstant N ρ ε - 9 * hairerSunsetConstant N ρ ε))
      (𝓝[>] 0) (𝓝 (constantsComparisonKappa L₁ L₂)) := by
  have h := (h₁.const_mul 3).sub (h₂.const_mul 9)
  unfold constantsComparisonKappa
  have heq :
      (fun ε : ℝ => 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε -
        (3 * hairerWickConstant N ρ ε - 9 * hairerSunsetConstant N ρ ε)) =
      (fun ε : ℝ => 3 * (wickConstant ρ ε - hairerWickConstant N ρ ε) -
        9 * (sunsetConstant ρ ε - hairerSunsetConstant N ρ ε)) := by
    funext ε
    ring
  rw [heq]
  exact h

end RegularityStructures.Phi43

end
