/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergencePathwiseNoise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# A measurable continuous-function-valued version of the massive heat convolution

Almost-sure space-time continuity and joint scalar measurability give a measurable random
continuous function. The construction changes only a measurable null set and agrees with the
pathwise convolution simultaneously at every space-time point outside that set.
The convolution is the stationary linear solution associated with equation (2.2) of the
statement; no existence theorem for the nonlinear equation is used.
-/

public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

theorem regularisedNoise_massiveHeatKernel_continuous_measurable_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) :
    ∃ Y : Ω → C(SpaceTime, ℝ), Measurable Y ∧
      ∀ᵐ ω ∂P, ∀ z : SpaceTime,
        Y ω z = ∫ w : SpaceTime, massiveHeatKernel (z - w) * ξ ω w := by
  classical
  let F : Ω → SpaceTime → ℝ := fun ω z =>
    ∫ w : SpaceTime, massiveHeatKernel (z - w) * ξ ω w
  have hcont : ∀ᵐ ω ∂P, Continuous (F ω) :=
    regularisedNoise_massiveHeatKernel_convolution_continuous_ae hW ρ hρ hε ξ hξ
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hcont)
  have hgood (ω : Ω) (hω : ω ∉ N) : Continuous (F ω) := by
    by_contra hn
    exact hω (hNsub hn)
  let Y : Ω → C(SpaceTime, ℝ) := fun ω =>
    if hω : ω ∈ N then 0 else ⟨F ω, hgood ω hω⟩
  refine ⟨Y, ?_, ?_⟩
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro z
    have hFm : Measurable (fun ω => F ω z) :=
      (regularisedNoise_massiveHeatKernel_convolution_measurable ρ ξ hξ).comp
        (measurable_id.prodMk measurable_const)
    have he : (fun ω => Y ω z) = N.piecewise (fun _ => (0 : ℝ)) (fun ω => F ω z) := by
      funext ω
      by_cases hω : ω ∈ N
      · simp only [Y, dite_eq_left hω, ContinuousMap.zero_apply, piecewise_eq_of_mem N _ _ hω]
      · simp only [Y, dite_eq_right hω, ContinuousMap.coe_mk, piecewise_eq_of_notMem N _ _ hω]
    rw [he]
    exact (measurable_const (a := (0 : ℝ))).piecewise hNm hFm
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hNzero] with ω hω
    intro z
    simp only [Y, dite_eq_right hω, ContinuousMap.coe_mk]
    rfl

theorem regularisedNoise_massiveHeatKernel_measurable_time_paths
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) :
    ∃ X : Ω → C(ℝ, C(Torus3, ℝ)), Measurable X ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ, ∀ x : Torus3,
        X ω t x = ∫ w : SpaceTime, massiveHeatKernel ((t, x) - w) * ξ ω w := by
  obtain ⟨Y, hYm, hY⟩ :=
    regularisedNoise_massiveHeatKernel_continuous_measurable_version hW ρ hρ hε ξ hξ
  refine ⟨fun ω => (Y ω).curry, ContinuousMap.continuous_curry.measurable.comp hYm, ?_⟩
  filter_upwards [hY] with ω hω
  intro t x
  exact hω (t, x)

end RegularityStructures.Phi43

end
