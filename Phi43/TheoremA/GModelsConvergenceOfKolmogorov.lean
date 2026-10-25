/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GModelsConvergenceAll
public import Phi43.BPHZ.ShiftedInputsAssembly
public import Phi43.BPHZ.BphzCauchyMoments
public import Phi43.Steps.RenormalisedCanonicalModel
public import Phi43.Steps.NoiseCauchy
public import Phi43.Stochastic.ConstantsComparisonLimits
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Dist
public import Phi43Statements.Defs.Phi43Size

/-!
# Convergence of the G-models from the Kolmogorov criterion

`phi43GModels_convergence_of_kolmogorov_modelNorm` proves the convergence of the G-models
(the statement `Statements.phi43GModels_convergence`, with universe `u` for the probability space)
from the Kolmogorov criterion for model norms alone (`KolmogorovModelNormStatement`, the statement
of `kolmogorov_modelNorm`, with index type in `Type` and probability space in `Type u`). The proof
does not use the Lipschitz continuity of the action. It applies
`phi43GModels_convergence_of_steps'` to the existence and uniqueness of the renormalised canonical
model (`renormalisedCanonicalModel_existsUnique`), the convergence of the noise potentials
(`phi43Noise_cauchy`), the comparison of the renormalisation constants
(`constantsComparison_limits`), the moment bounds for the regularised trees, packaged as
`shiftedBphzInputs_of_bphzCauchyMoments bphzCauchyMoments_holds`, and the power rates for the
constant differences (`constantDifferencePowerRate_holds`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

universe u

set_option linter.unusedVariables false in
/-- **Convergence of the G-models from the Kolmogorov criterion for model norms.** -/
theorem phi43GModels_convergence_of_kolmogorov_modelNorm (hG5 : Phi43.KolmogorovModelNormStatement.{u, 0}) :
    ∀ (κ : RegularityStructures.Phi43.Kappa)
    (hκE : κ.1 ∉ RegularityStructures.Phi43.Statements.excludedKappa) (N : ℕ) (hN : 5 ≤ N)
    (η : RegularityStructures.NegExponent)
    (hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ))) (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (ρ ρ' : RegularityStructures.ParabolicSpace → ℝ)
    (hρ : RegularityStructures.Phi43.IsMollifier ρ) (hρ' : RegularityStructures.Phi43.IsMollifier ρ')
    (c : RegularityStructures.Phi43.RenormalisationConstants),
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
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
              (Z ((2 : ℝ) ^ n)⁻¹ ω) (ψ ((2 : ℝ) ^ n)⁻¹ ω) ≤ ENNReal.ofReal B := by
  have hG1 : Phi43.RenormalisedCanonicalModelStatement := fun N κ noise Cg q hg C =>
    renormalisedCanonicalModel_existsUnique N κ noise Cg q hg C
  have hG7 : Phi43.NoiseCauchyStatement.{u} := phi43Noise_cauchy
  have hG8 : Phi43.ConstantsComparisonStatement := constantsComparison_limits
  exact Phi43.phi43GModels_convergence_of_steps' hG1 hG5 hG7 hG8
    (shiftedBphzInputs_of_bphzCauchyMoments bphzCauchyMoments_holds)

end RegularityStructures.Phi43

end
