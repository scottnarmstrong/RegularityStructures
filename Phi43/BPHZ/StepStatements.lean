/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.ExcludedKappa
public import Phi43Statements.Defs.HasPhi43NoiseGrowth
public import RegularityStructures.Statements.Defs.IsMassivePotential
public import Phi43Statements.Defs.IsModeratePhi43ModelOf
public import Phi43Statements.Defs.IsModerateRenormalisedCanonicalModel
public import RegularityStructures.Statements.Defs.ParabolicThickening
public import Phi43Statements.Defs.Phi43NoiseDist
public import Phi43Statements.Defs.Phi43NoiseSize
public import RegularityStructures.Probability.ModelKolmogorovNorm
public import RegularityStructures.Probability.WhiteNoise
public import Phi43.Mollifier
public import Phi43.Constants
public import Phi43.Stochastic.ConstantsComparisonDefinitions
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Intermediate statements as propositions

The statements of three intermediate results of the proof of Theorem A, copied verbatim as closed
propositions (universe-explicit where the statement quantifies over a probability space):

* `RenormalisedCanonicalModelStatement`: existence and uniqueness of the renormalised canonical
  model (`renormalisedCanonicalModel_existsUnique`);
* `NoiseCauchyStatement`: the Cauchy property of the regularised noises (`phi43Noise_cauchy`);
* `ConstantsComparisonStatement`: the comparison of the renormalisation constants
  (`constantsComparison`).

The conditional assembly `phi43GModels_convergence_of_steps'` takes them as hypotheses.
-/

@[expose] public section

universe u

-- The statements name hypotheses that the propositions do not use.
set_option linter.unusedVariables false

open scoped Topology

namespace RegularityStructures.Phi43

def RenormalisedCanonicalModelStatement : Prop :=
  ∀ (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
    (noise : RegularityStructures.Phi43.CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : RegularityStructures.ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + RegularityStructures.parabolicNorm z) ^ q)
    (C : RegularityStructures.Phi43.RenormalisationConstants),
    (∃ Z : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
        RegularityStructures.parabolicSemigroup,
      RegularityStructures.Phi43.Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z) ∧
    ∀ Z Z' : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
        RegularityStructures.parabolicSemigroup,
      RegularityStructures.Phi43.Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z →
      RegularityStructures.Phi43.Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z' →
        Z.diffNormOn Z' (RegularityStructures.Phi43.gamma κ) Set.univ = 0

def NoiseCauchyStatement : Prop :=
  ∀ (η : RegularityStructures.NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ)),
    (∀ f : RegularityStructures.SpaceTime → ℝ, RegularityStructures.IsSmoothOnSpaceTime f →
      RegularityStructures.Phi43.Statements.HasPhi43NoiseGrowth f →
      ∃ ψ : ℝ → C(RegularityStructures.Torus3, ℝ),
        RegularityStructures.IsMassivePotential f ψ ∧
        RegularityStructures.IsSmoothOnSpaceTime
          (fun z : RegularityStructures.SpaceTime => ψ z.1 z.2) ∧
        Continuous ψ) ∧
    (∀ ρ : RegularityStructures.ParabolicSpace → ℝ, RegularityStructures.Phi43.IsMollifier ρ →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
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
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
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
                ENNReal.ofReal (C * max ε ε' ^ (β₀ * p))

def ConstantsComparisonStatement : Prop :=
∀ N : ℕ, ∃ L₁ L₂ κ : ℝ, ∀ (ρ : RegularityStructures.ParabolicSpace → ℝ),
      RegularityStructures.Phi43.IsMollifier ρ →
      Filter.Tendsto (fun ε : ℝ => RegularityStructures.Phi43.wickConstant ρ ε -
          RegularityStructures.Phi43.hairerWickConstant N ρ ε) (𝓝[>] 0) (𝓝 L₁) ∧
      Filter.Tendsto (fun ε : ℝ => RegularityStructures.Phi43.sunsetConstant ρ ε -
          RegularityStructures.Phi43.hairerSunsetConstant N ρ ε) (𝓝[>] 0) (𝓝 L₂) ∧
      Filter.Tendsto
        (fun ε : ℝ => 3 * RegularityStructures.Phi43.wickConstant ρ ε -
            9 * RegularityStructures.Phi43.sunsetConstant ρ ε -
          (3 * RegularityStructures.Phi43.hairerWickConstant N ρ ε -
            9 * RegularityStructures.Phi43.hairerSunsetConstant N ρ ε))
        (𝓝[>] 0) (𝓝 κ)

end RegularityStructures.Phi43

end
