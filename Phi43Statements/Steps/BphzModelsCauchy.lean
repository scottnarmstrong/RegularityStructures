/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.ExcludedKappa
public import Phi43Statements.Defs.IsModeratePhi43ModelOf
public import RegularityStructures.Probability.ModelKolmogorovNorm
public import RegularityStructures.Probability.WhiteNoise
public import Phi43.Mollifier
public import Phi43.Stochastic.ConstantsComparisonDefinitions
public import Phi43.Steps.BphzModelsCauchy

/-!
# Convergence of the BPHZ models

The renormalised canonical models of the regularised noises, renormalised with Hairer's constants
`C₁^{ε,K}`, `C₂^{ε,K}` [Hai14, (10.33), (10.41)] (`hairerWickConstant`, `hairerSunsetConstant`),
form a Cauchy family in `L^p`. Let `ρ`, `ρ'` be mollifiers, with regularised noises driven by the
same white noise, and let `Z ε`, `Z' ε'` be these models at scales `ε`, `ε'`. Then on every compact
set the `p`-th moments of the model norms are bounded uniformly in `ε`, and
`E ‖Z ε; Z' ε'‖^p ≤ C max(ε, ε')^{θp}`. In particular the models converge in probability, and
the limit does not depend on the mollifier.

This is [Hai14, Theorem 10.22]. In the proof of Theorem A, together with the comparison of the
renormalisation constants, it gives the convergence of the models renormalised with the constants
of the statement.

Here `κ ∈ (0, 1/16)` fixes the homogeneity `-5/2 - κ` of the noise symbol `Ξ` in the Φ⁴₃ regularity
structure `phi43RegularityStructure κ`, the cutoff of the fixed point is `γ = gamma κ = 1 + 3κ`, and
`N` fixes the truncated heat kernel `annKernel0C N` of the kernel decomposition [Hai14, Assumption
5.4].

The proof is `RegularityStructures.Phi43.bphzModels_cauchy`,
in the module `Phi43.Steps.BphzModelsCauchy`.

Source: [Hai14, Theorem 10.22, (10.33), (10.41)].
-/

public section

namespace RegularityStructures.Phi43

/-- **Cauchy property of the BPHZ models.** The models renormalised with Hairer's constants
have uniformly bounded moments on every compact set. Two of them, at scales `ε` and `ε'`, for
mollifiers `ρ` and `ρ'` and driven by the same white noise, are `max(ε, ε')^θ`-close in `L^p`. -/
theorem Statements.bphzModels_cauchy (κ : RegularityStructures.Phi43.Kappa)
    (hκE : κ.1 ∉ RegularityStructures.Phi43.Statements.excludedKappa)
    (N : ℕ) (hN : 5 ≤ N) (ρ ρ' : RegularityStructures.ParabolicSpace → ℝ)
    (hρ : RegularityStructures.Phi43.IsMollifier ρ) (hρ' : RegularityStructures.Phi43.IsMollifier ρ')
    (S : Set RegularityStructures.ParabolicSpace) (hS : IsCompact S) (p : ℕ) (hp : 1 ≤ p) :
    ∃ θ C : ℝ, 0 < θ ∧ 0 ≤ C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure P] (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ),
      RegularityStructures.IsWhiteNoise P W →
      ∀ (ξ ξ' : ℝ → Ω → RegularityStructures.SpaceTime → ℝ),
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε)) →
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ' ε (ξ' ε)) →
      ∀ (Z Z' : ℝ → Ω → RegularityStructures.Model
          (RegularityStructures.Phi43.phi43RegularityStructure κ)
          RegularityStructures.parabolicSemigroup),
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
          RegularityStructures.Phi43.Statements.IsModeratePhi43ModelOf N κ (ξ ε ω)
            (RegularityStructures.Phi43.hairerWickConstant N ρ ε,
              RegularityStructures.Phi43.hairerSunsetConstant N ρ ε) (Z ε ω)) →
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
          RegularityStructures.Phi43.Statements.IsModeratePhi43ModelOf N κ (ξ' ε ω)
            (RegularityStructures.Phi43.hairerWickConstant N ρ' ε,
              RegularityStructures.Phi43.hairerSunsetConstant N ρ' ε) (Z' ε ω)) →
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ε' ∈ Set.Ioc (0 : ℝ) 1,
        AEMeasurable (fun ω => (Z ε ω).normOn (RegularityStructures.Phi43.gamma κ) S) P ∧
        AEMeasurable
          (fun ω => (Z ε ω).diffNormOn (Z' ε' ω) (RegularityStructures.Phi43.gamma κ) S) P ∧
        ∫⁻ ω, (Z ε ω).normOn (RegularityStructures.Phi43.gamma κ) S ^ p ∂P ≤ ENNReal.ofReal C ∧
        ∫⁻ ω, (Z ε ω).diffNormOn (Z' ε' ω) (RegularityStructures.Phi43.gamma κ) S ^ p ∂P ≤
          ENNReal.ofReal (C * max ε ε' ^ (θ * p)) :=
  by exact RegularityStructures.Phi43.bphzModels_cauchy κ hκE N hN ρ ρ' hρ hρ' S hS p hp

end RegularityStructures.Phi43

end
