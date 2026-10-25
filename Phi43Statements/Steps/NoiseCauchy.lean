/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.HasPhi43NoiseGrowth
public import RegularityStructures.Statements.Defs.IsMassivePotential
public import Phi43Statements.Defs.Phi43NoiseSize
public import Phi43Statements.Defs.Phi43NoiseDist
public import RegularityStructures.Probability.WhiteNoise
public import Phi43.Mollifier
public import Phi43.Steps.NoiseCauchy

/-!
# Convergence of the massive potentials of the noise

(a) Every smooth noise `f` with polynomial growth (`HasPhi43NoiseGrowth`) has a massive heat
potential `ψ = G * f` (`IsMassivePotential`), smooth on `ℝ × T³` and continuous as a path in
`C(T³)`.
(b) For every mollifier and every `ε ∈ (0, 1]`, the regularised noise has polynomial growth almost
surely, on a measurable event.
(c) There is `β₀ > 0`, depending only on `η`, such that the potentials of the regularised noises
have bounded moments of their size `phi43NoiseSize`, and
`E N_(T)(ψ_ε - ψ'_{ε'})^p ≤ C max(ε, ε')^{β₀ p}`, also for two different mollifiers.

The potential `G * ξ_ε` plays the role of the term `K * ξ` whose regularity in `𝒞^η` the solution
theory requires [Hai14, Proposition 9.8, (9.19)]. In the proof of Theorem A it is the noise
component of the lifts.

The proof is `RegularityStructures.Phi43.phi43Noise_cauchy`,
in the module `Phi43.Steps.NoiseCauchy`.

Source: [Hai14, Proposition 9.8].
-/

public section

namespace RegularityStructures.Phi43

/-- **Convergence of the potentials.** (a) Every smooth noise with polynomial growth has a
massive heat potential, smooth on `ℝ × T³` and continuous into `C(T³)`. (b) For every
`ε ∈ (0, 1]` the regularised noise has polynomial growth almost surely, on a measurable event.
(c) There is `β₀ > 0`, depending only on `η`, such that the potentials have bounded moments of
`N_(T)` and are `max(ε, ε')^{β₀}`-Cauchy in `L^p`, across mollifiers. -/
theorem Statements.phi43Noise_cauchy (η : RegularityStructures.NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ)) :
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
          (∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε)) →
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
                ENNReal.ofReal (C * max ε ε' ^ (β₀ * p)) :=
  by exact RegularityStructures.Phi43.phi43Noise_cauchy η hη

end RegularityStructures.Phi43

end
