/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonCausalLimits
public import Phi43.Stochastic.ConstantsComparisonC2Majorants
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# Unconditional comparison of the second renormalisation constants

The comparison of the second constants in Section 7 of the statement, for the causal kernel of
[Hai14, Lemma 5.5].
The limiting covariances are defined from the unregularised kernels. Causal time cuts give their
almost-everywhere limits, and the order-three and order-four majorants give dominated convergence
for the difference of Hairer's (10.41). The resulting finite limit depends on `N` and not on `ρ`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.Phi43

/-- Covariance of the unregularised massive kernel, away from its singular base point. -/
def constantsComparison_covarianceLimit (z : SpaceTime) : ℝ :=
  ∫ w, massiveHeatKernel (z + w) * massiveHeatKernel w

/-- Covariance of the unregularised causal Hairer kernel. -/
def constantsComparison_hairerCovarianceLimit (N : ℕ) (z : SpaceTime) : ℝ :=
  ∫ w, hairerKernelTorus N (z + w) * hairerKernelTorus N w

/-- The finite, mollifier-independent difference of the constants in (10.41). -/
def constantsComparison_sunsetLimit (N : ℕ) : ℝ :=
  2 * (∫ z, constantsComparisonR N z * constantsComparison_covarianceLimit z ^ 2) +
    2 * (∫ z, hairerKernelTorus N z *
      (constantsComparison_covarianceLimit z - constantsComparison_hairerCovarianceLimit N z) *
      (constantsComparison_covarianceLimit z + constantsComparison_hairerCovarianceLimit N z))

private theorem comparisonC2_ae_time_ne_zero :
    ∀ᵐ z : SpaceTime ∂volume, z.1 ≠ 0 := by
  exact (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := (volume : Measure Torus3))).ae (Measure.ae_ne (volume : Measure ℝ) (0 : ℝ))

theorem constantsComparison_covariance_tendsto_ae
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) :
    ∀ᵐ z ∂volume, Tendsto (fun ε : ℝ => covariance ρ ε z)
      (𝓝[>] 0) (𝓝 (constantsComparison_covarianceLimit z)) := by
  obtain ⟨C, hC, hG⟩ := massiveHeatKernel_global_singular_bound
  have hcausal : ∀ w : SpaceTime, w.1 ≤ 0 → massiveHeatKernel w = 0 := by
    intro w hw
    simp [massiveHeatKernel, not_lt.mpr hw]
  have hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ w, 0 < torusParabolicSize w →
      |massiveHeatKernel w| ≤ C * torusParabolicSize w ^ (-(3 : ℝ)) := by
    refine ⟨C, hC, ?_⟩
    intro w hw
    rw [abs_of_nonneg (massiveHeatKernel_nonneg w)]
    exact hG w hw
  filter_upwards [comparisonC2_ae_time_ne_zero] with z hz
  have h := constantsComparison_causal_covariance_tendsto ρ hρ
    measurable_massiveHeatKernel integrable_massiveHeatKernel
    constantsComparison_massiveHeatKernel_memLp_fourThirds hcausal hbound hz
  simp_rw [constantsComparison_mollifiedKernel_eq_convolution ρ] at h
  exact h

theorem constantsComparison_hairerCovariance_tendsto_ae
    (N : ℕ) (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) :
    ∀ᵐ z ∂volume, Tendsto (fun ε : ℝ => hairerCovariance N ρ ε z)
      (𝓝[>] 0) (𝓝 (constantsComparison_hairerCovarianceLimit N z)) := by
  have hcausal : ∀ w : SpaceTime, w.1 ≤ 0 → hairerKernelTorus N w = 0 := by
    intro w hw
    simp [hairerKernelTorus, hairerKernel, annShellC_eq_zero_of_nonpos, hw]
  have hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ w, 0 < torusParabolicSize w →
      |hairerKernelTorus N w| ≤ C * torusParabolicSize w ^ (-(3 : ℝ)) := by
    obtain ⟨C, hC, hK⟩ :=
      constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
    exact ⟨C, hC, fun _ hw => hK hw⟩
  filter_upwards [comparisonC2_ae_time_ne_zero] with z hz
  have h := constantsComparison_causal_covariance_tendsto ρ hρ
    (measurable_constantsComparison_hairerKernelTorus N)
    (integrable_constantsComparison_hairerKernelTorus N)
    (constantsComparison_hairerKernelTorus_memLp_fourThirds N) hcausal hbound hz
  simp_rw [constantsComparison_hairerMollifiedKernel_eq_convolution N ρ] at h
  exact h

private def comparisonC2_data
    (N : ℕ) (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) :
    ConstantsComparisonC2Data N ρ where
  covariance_limit := constantsComparison_covarianceLimit
  hairer_covariance_limit := constantsComparison_hairerCovarianceLimit N
  covariance_tendsto := constantsComparison_covariance_tendsto_ae ρ hρ
  hairer_covariance_tendsto := constantsComparison_hairerCovariance_tendsto_ae N ρ hρ
  massive_integrable := fun hε hε1 =>
    (constantsComparison_C2_integrability N ρ hρ hε hε1).1
  hairer_integrable := fun hε hε1 =>
    (constantsComparison_C2_integrability N ρ hρ hε hε1).2.1
  remainder_integrable := fun hε hε1 =>
    (constantsComparison_C2_integrability N ρ hρ hε hε1).2.2.1
  correction_integrable := fun hε hε1 =>
    (constantsComparison_C2_integrability N ρ hρ hε hε1).2.2.2
  first_measurable := fun hε hε1 =>
    (constantsComparison_C2_integrability N ρ hρ hε hε1).2.2.1.aestronglyMeasurable
  second_measurable := fun hε hε1 =>
    (constantsComparison_C2_integrability N ρ hρ hε hε1).2.2.2.aestronglyMeasurable
  first_bound := constantsComparison_C2_first_majorant N ρ hρ
  second_bound := constantsComparison_C2_second_majorant N ρ hρ

/-- The second-constant difference converges to a finite limit independent of the mollifier. -/
theorem constantsComparison_sunsetLimit_tendsto
    (N : ℕ) (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) :
    Tendsto (fun ε : ℝ => sunsetConstant ρ ε - hairerSunsetConstant N ρ ε)
      (𝓝[>] 0) (𝓝 (constantsComparison_sunsetLimit N)) :=
  constantsComparison_sunset_tendsto N ρ (comparisonC2_data N ρ hρ)

end RegularityStructures.Phi43

end
