/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.ExcludedKappa
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Size
public import Phi43Statements.Defs.Phi43Dist
public import RegularityStructures.Probability.WhiteNoise
public import Phi43.Mollifier
public import Phi43.Constants
public import Phi43.TheoremA.GModelsConvergenceOfKolmogorov
public import RegularityStructures.Probability.ModelKolmogorov

/-!
# Convergence of the G-models

The lifts formed by the G-models (the canonical models renormalised with the constants of the
statement, shifted by a fixed pair) and the massive potentials of the regularised noises have tight
sizes and are Cauchy in probability, also for two different mollifiers, and almost surely along the
dyadic scales. The theorem `phi43GModels_convergence` has exactly the statement
`Statements.phi43GModels_convergence` of `Phi43Statements.Steps.GModelsConvergence`. It is
`phi43GModels_convergence_of_kolmogorov_modelNorm` applied to the Kolmogorov criterion for the model
norms, `kolmogorov_modelNorm`.

Source: [Hai14, Theorem 10.22]; the statement, Theorem A.
-/

public section

namespace RegularityStructures.Phi43

open scoped Topology

/-- **Convergence of the G-models**: tightness of the lift sizes, the Cauchy property in probability
for `phi43Dist`, and almost sure convergence along the dyadic scales. -/
theorem phi43GModels_convergence (κ : RegularityStructures.Phi43.Kappa)
    (hκE : κ.1 ∉ RegularityStructures.Phi43.Statements.excludedKappa) (N : ℕ) (hN : 5 ≤ N)
    (η : RegularityStructures.NegExponent)
    (hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ))) (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (ρ ρ' : RegularityStructures.ParabolicSpace → ℝ)
    (hρ : RegularityStructures.Phi43.IsMollifier ρ) (hρ' : RegularityStructures.Phi43.IsMollifier ρ')
    (c : RegularityStructures.Phi43.RenormalisationConstants) :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure P] (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ),
      RegularityStructures.IsWhiteNoise P W →
      ∀ (ξ ξ' : ℝ → Ω → RegularityStructures.SpaceTime → ℝ),
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε)) →
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ' ε (ξ' ε)) →
      ∀ (Z Z' : ℝ → Ω → RegularityStructures.Model
          (RegularityStructures.Phi43.phi43RegularityStructure κ)
          RegularityStructures.parabolicSemigroup)
        (ψ ψ' : ℝ → Ω → ℝ → C(RegularityStructures.Torus3, ℝ)),
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
          RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (ξ ε ω)
            (RegularityStructures.Phi43.wickConstant ρ ε + c.1,
              RegularityStructures.Phi43.sunsetConstant ρ ε + c.2) (Z ε ω) (ψ ε ω)) →
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
          RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ (ξ' ε ω)
            (RegularityStructures.Phi43.wickConstant ρ' ε + c.1,
              RegularityStructures.Phi43.sunsetConstant ρ' ε + c.2) (Z' ε ω) (ψ' ε ω)) →
        (∀ T : ℝ, 1 ≤ T → ∀ ϑ : ℝ, 0 < ϑ → ∃ B : ℝ, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
          P {ω | ENNReal.ofReal B <
            RegularityStructures.Phi43.Statements.phi43Size κ η T (Z ε ω) (ψ ε ω)} ≤
              ENNReal.ofReal ϑ) ∧
        (∀ T : ℝ, 1 ≤ T → ∀ δ : ℝ, 0 < δ →
          Filter.Tendsto (fun e : ℝ × ℝ =>
              P {ω | ENNReal.ofReal δ < RegularityStructures.Phi43.Statements.phi43Dist κ η T
                (Z e.1 ω) (Z' e.2 ω) (ψ e.1 ω) (ψ' e.2 ω)})
            ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 0)) ∧
        ∀ᵐ ω ∂P, ∀ T : ℕ, 1 ≤ T →
          (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
            RegularityStructures.Phi43.Statements.phi43Dist κ η T
              (Z ((2 : ℝ) ^ n)⁻¹ ω) (Z ((2 : ℝ) ^ m)⁻¹ ω)
              (ψ ((2 : ℝ) ^ n)⁻¹ ω) (ψ ((2 : ℝ) ^ m)⁻¹ ω) ≤ ENNReal.ofReal δ) ∧
          ∃ B : ℝ, ∀ n : ℕ,
            RegularityStructures.Phi43.Statements.phi43Size κ η T
              (Z ((2 : ℝ) ^ n)⁻¹ ω) (ψ ((2 : ℝ) ^ n)⁻¹ ω) ≤ ENNReal.ofReal B :=
  phi43GModels_convergence_of_kolmogorov_modelNorm
    (fun {ι} i1 i2 => @kolmogorov_modelNorm ι i1 i2) κ hκE N hN η hη hκη ρ ρ' hρ hρ' c

end RegularityStructures.Phi43

end
