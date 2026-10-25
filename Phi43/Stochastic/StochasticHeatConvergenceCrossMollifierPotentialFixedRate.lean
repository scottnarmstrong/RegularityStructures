/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceCrossMollifierFixedRate
public import Phi43.Stochastic.StochasticHeatConvergenceCrossMollifierPotential
public import RegularityStructures.Statements.Defs.IsMassivePotential
public import Phi43Statements.Defs.Phi43NoiseDist
public import Phi43Statements.Defs.Phi43NoiseSize
public import Mathlib.Order.CompletePartialOrder
public import Phi43.Stochastic.StochasticHeatConvergenceContinuousVersion
public import Phi43.Stochastic.StochasticHeatConvergencePathwiseIdentification

/-!
# Fixed-rate window moments for massive-potential representatives

This is the representative-independent form of the cross-mollifier component of the convergence
of the noise potentials, [Hai14, Proposition 9.5, (9.15)].  The potential identity is
used only to replace arbitrary representatives by continuous measurable stationary versions on one
full-measure set.
-/

public noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace RegularityStructures.Phi43

private theorem fixedRate_potential_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (ψ : Ω → ℝ → C(Torus3, ℝ))
    (hψ : ∀ᵐ ω ∂P, ∀ t x, ψ ω t x =
      ∫ w : SpaceTime, massiveHeatKernel ((t, x) - w) * ξ ω w) :
    ∃ X : Ω → C(ℝ, C(Torus3, ℝ)), Measurable X ∧
      (ψ =ᵐ[P] fun ω t => X ω t) ∧
      ∀ t x, (fun ω => X ω t x) =ᵐ[P] stationaryField W ρ ε (t, x) := by
  obtain ⟨X, hXm, hraw⟩ :=
    regularisedNoise_massiveHeatKernel_measurable_time_paths hW ρ hρ hε ξ hξ
  refine ⟨X, hXm, ?_, ?_⟩
  · filter_upwards [hψ, hraw] with ω hω hω'
    funext t
    ext x
    exact (hω t x).trans (hω' t x).symm
  · intro t x
    filter_upwards [hraw,
      regularisedNoise_massiveHeatKernel_convolution_ae hW ρ hρ hε ξ hξ (t, x)] with ω hω hω'
    exact (hω t x).trans hω'

theorem regularisedNoise_massivePotential_window_moments_fixed_rate
    (η : NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ)) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
    ∀ ρ ρ' : ParabolicSpace → ℝ,
      IsMollifier ρ → IsMollifier ρ' →
      ∀ T : ℝ, 1 ≤ T → ∀ p : ℕ, 1 ≤ p →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (SpaceTime → ℝ) → Ω → ℝ), IsWhiteNoise P W →
        ∀ (ξ ξ' : ℝ → Ω → SpaceTime → ℝ),
          (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
            IsRegularisedNoise P W ρ ε (ξ ε)) →
          (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
            IsRegularisedNoise P W ρ' ε (ξ' ε)) →
          ∀ (ψ ψ' : ℝ → Ω → ℝ → C(Torus3, ℝ)),
            (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
              RegularityStructures.IsMassivePotential (ξ ε ω) (ψ ε ω)) →
            (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
              RegularityStructures.IsMassivePotential (ξ' ε ω) (ψ' ε ω)) →
            ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
              ∀ ε' ∈ Set.Ioc (0 : ℝ) 1,
              AEMeasurable (fun ω => Statements.phi43NoiseSize η T (ψ ε ω)) P ∧
              AEMeasurable (fun ω => Statements.phi43NoiseDist η T
                (ψ ε ω) (ψ' ε' ω)) P ∧
              ∫⁻ ω, Statements.phi43NoiseSize η T (ψ ε ω) ^ p ∂P ≤
                ENNReal.ofReal C ∧
              ∫⁻ ω, Statements.phi43NoiseDist η T
                (ψ ε ω) (ψ' ε' ω) ^ p ∂P ≤
                ENNReal.ofReal (C * max ε ε' ^ (β₀ * p)) := by
  obtain ⟨β₀, hβ₀, hfield⟩ :=
    stationaryField_version_window_cross_moment_bound_fixed_rate η hη
  refine ⟨β₀, hβ₀, ?_⟩
  intro ρ ρ' hρ hρ' T hT p hp
  obtain ⟨βold, Cold, hβold, hCold, hold⟩ :=
    regularisedNoise_massivePotential_window_moments ρ ρ' hρ hρ' η hη T hT p hp
  obtain ⟨Cd, hCd, hfieldBound⟩ := hfield ρ ρ' hρ hρ' T hT p hp
  refine ⟨Cold + Cd, add_nonneg hCold hCd, ?_⟩
  intro Ω _ P hP W hW ξ ξ' hξ hξ' ψ ψ' hψ hψ' ε hε ε' hε'
  have hψε : ∀ᵐ ω ∂P,
      RegularityStructures.IsMassivePotential (ξ ε ω) (ψ ε ω) := hψ ε hε
  have hψ'ε' : ∀ᵐ ω ∂P,
      RegularityStructures.IsMassivePotential (ξ' ε' ω) (ψ' ε' ω) := hψ' ε' hε'
  have hψεeq : ∀ᵐ ω ∂P, ∀ t x,
      (ψ ε) ω t x = ∫ w : SpaceTime,
        massiveHeatKernel ((t, x) - w) * (ξ ε) ω w :=
    hψε.mono fun ω hω => hω.2
  have hψ'ε'eq : ∀ᵐ ω ∂P, ∀ t x,
      (ψ' ε') ω t x = ∫ w : SpaceTime,
        massiveHeatKernel ((t, x) - w) * (ξ' ε') ω w :=
    hψ'ε'.mono fun ω hω => hω.2
  have hold' := hold hW (ε := ε) (ε' := ε') hε.1 hε.2 hε'.1 hε'.2
    (ξ ε) (ξ' ε') (hξ ε hε) (hξ' ε' hε') (ψ ε) (ψ' ε')
    hψεeq hψ'ε'eq
  rcases hold' with ⟨hsize_meas, hdist_meas, hsize, _hold_dist⟩
  obtain ⟨X, hXm, hXae, hX⟩ := fixedRate_potential_version hW ρ hρ hε.1
    (ξ ε) (hξ ε hε) (ψ ε) hψεeq
  obtain ⟨Y, hYm, hYae, hY⟩ := fixedRate_potential_version hW ρ' hρ' hε'.1
    (ξ' ε') (hξ' ε' hε') (ψ' ε') hψ'ε'eq
  have hAd : (fun ω => Statements.phi43NoiseDist η T (ψ ε ω) (ψ' ε' ω)) =ᵐ[P]
      (fun ω => ⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
        holderBesovENorm η (X ω t - Y ω t)) := by
    filter_upwards [hXae, hYae] with ω hω hω'
    simp only [Statements.phi43NoiseDist]
    rw [hω, hω']
  have hfixed := hfieldBound hW
    (ε := ε) (ε' := ε') hε.1 hε.2 hε'.1 hε'.2 X Y hXm hYm hX hY
  refine ⟨hsize_meas, hdist_meas, ?_, ?_⟩
  · exact hsize.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hCd))
  · calc
      _ = ∫⁻ ω, (⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
          holderBesovENorm η (X ω t - Y ω t)) ^ p ∂P :=
        lintegral_congr_ae (hAd.fun_comp fun a : ℝ≥0∞ => a ^ p)
      _ ≤ ENNReal.ofReal (Cd * max ε ε' ^ (β₀ * p)) := hfixed
      _ ≤ ENNReal.ofReal ((Cold + Cd) * max ε ε' ^ (β₀ * p)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCold)
          (rpow_nonneg (le_trans hε.1.le (le_max_left _ _)) _)

end RegularityStructures.Phi43

end
