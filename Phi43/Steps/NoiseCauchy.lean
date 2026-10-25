/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergencePotentialSmooth
public import Phi43.Stochastic.StochasticHeatConvergenceGrowthMeasurable
public import Phi43.Stochastic.StochasticHeatConvergenceCrossMollifierPotentialFixedRate

/-!
# Convergence of the massive potentials of the noise

Smooth noises of polynomial growth have smooth massive heat potentials; the regularised noises have
polynomial growth almost surely; and the potentials of the regularised noises have bounded moments
of their size and converge in `L^p` at a rate `max(ε, ε')^{β₀}`, also for two different mollifiers.
The theorem `phi43Noise_cauchy` has exactly the statement `Statements.phi43Noise_cauchy` of
`Phi43Statements.Steps.NoiseCauchy`, with the same quantifier order.

Source: [Hai14, Proposition 9.5, Proposition 9.8].
-/

public noncomputable section

namespace RegularityStructures.Phi43

/-- **Convergence of the massive potentials of the noise**: existence of smooth potentials,
measurable polynomial growth of the regularised noises, and uniform moments and a rate for the
potentials. -/
theorem phi43Noise_cauchy (η : RegularityStructures.NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ)) :
    (∀ f : RegularityStructures.SpaceTime → ℝ, RegularityStructures.IsSmoothOnSpaceTime f →
      RegularityStructures.Phi43.Statements.HasPhi43NoiseGrowth f →
      ∃ ψ : ℝ → C(RegularityStructures.Torus3, ℝ),
        RegularityStructures.IsMassivePotential f ψ ∧
        RegularityStructures.IsSmoothOnSpaceTime
          (fun z : RegularityStructures.SpaceTime => ψ z.1 z.2) ∧
        Continuous ψ) ∧
    (∀ ρ : RegularityStructures.ParabolicSpace → ℝ, RegularityStructures.Phi43.IsMollifier ρ →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P] (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ),
        RegularityStructures.IsWhiteNoise P W →
        ∀ ξ : ℝ → Ω → RegularityStructures.SpaceTime → ℝ,
          (∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε)) →
          ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
            MeasurableSet {ω | RegularityStructures.Phi43.Statements.HasPhi43NoiseGrowth (ξ ε ω)} ∧
            ∀ᵐ ω ∂P, RegularityStructures.Phi43.Statements.HasPhi43NoiseGrowth (ξ ε ω)) ∧
    ∃ β₀ : ℝ, 0 < β₀ ∧
    ∀ ρ ρ' : RegularityStructures.ParabolicSpace → ℝ, RegularityStructures.Phi43.IsMollifier ρ →
      RegularityStructures.Phi43.IsMollifier ρ' → ∀ T : ℝ, 1 ≤ T → ∀ p : ℕ, 1 ≤ p →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P] (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ),
        RegularityStructures.IsWhiteNoise P W →
        ∀ (ξ ξ' : ℝ → Ω → RegularityStructures.SpaceTime → ℝ),
          (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
            RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε)) →
          (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
            RegularityStructures.Phi43.IsRegularisedNoise P W ρ' ε (ξ' ε)) →
          ∀ (ψ ψ' : ℝ → Ω → ℝ → C(RegularityStructures.Torus3, ℝ)),
            (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
              RegularityStructures.IsMassivePotential (ξ ε ω) (ψ ε ω)) →
            (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
              RegularityStructures.IsMassivePotential (ξ' ε ω) (ψ' ε ω)) →
            ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ε' ∈ Set.Ioc (0 : ℝ) 1,
              AEMeasurable
                (fun ω => RegularityStructures.Phi43.Statements.phi43NoiseSize η T (ψ ε ω)) P ∧
              AEMeasurable (fun ω =>
                RegularityStructures.Phi43.Statements.phi43NoiseDist η T (ψ ε ω) (ψ' ε' ω)) P ∧
              ∫⁻ ω, RegularityStructures.Phi43.Statements.phi43NoiseSize η T (ψ ε ω) ^ p ∂P ≤
                ENNReal.ofReal C ∧
              ∫⁻ ω, RegularityStructures.Phi43.Statements.phi43NoiseDist η T (ψ ε ω) (ψ' ε' ω) ^ p ∂P ≤
                ENNReal.ofReal (C * max ε ε' ^ (β₀ * p)) := by
  refine ⟨?_, ?_⟩
  · intro f hf hg
    exact massivePotential_exists_smooth_of_polynomialLift_growth f hf hg
  · refine ⟨?_, ?_⟩
    · intro ρ hρ Ω _ P hP W hW ξ hξ ε hε
      exact regularisedNoise_hasPhi43NoiseGrowth_measurable_ae P W hW ρ hρ hε
        (ξ ε) (hξ ε hε)
    · exact regularisedNoise_massivePotential_window_moments_fixed_rate η hη

end RegularityStructures.Phi43

end
