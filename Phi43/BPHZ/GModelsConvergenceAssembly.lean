/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GModelsConvergenceOfRate
public import Phi43.Stochastic.ConstantsRate
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Dist
public import Phi43Statements.Defs.Phi43Size

/-!
# Convergence of the G-models through the shifted BPHZ models

`constantDifferencePowerRate_holds` discharges the power-rate hypothesis of
`phi43GModels_convergence_of_steps'_of_shiftRate` from `constantsRate_wick` and
`constantsRate_sunset` (rates `ε^{θ'}` for the Wick and sunset constant differences), so
`phi43GModels_convergence_of_steps'` concludes the convergence of the G-models from the existence
and uniqueness of the renormalised canonical model, the Kolmogorov bound for the model norms, the
Cauchy property of the noises, the comparison of the renormalisation constants and the shifted
moment inputs alone.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

universe u

namespace RegularityStructures.Phi43

/-- The constant differences converge at a power rate (both with the same exponent). -/
theorem constantDifferencePowerRate_holds : ConstantDifferencePowerRate := by
  intro N ρ hρ
  obtain ⟨C₁, θ₁, hθ₁, h₁⟩ := RegularityStructures.Phi43.constantsRate_wick N ρ hρ
  obtain ⟨C₂, θ₂, hθ₂, h₂⟩ := RegularityStructures.Phi43.constantsRate_sunset N ρ hρ
  refine ⟨RegularityStructures.Phi43.constantsComparison_wickLimit N,
    RegularityStructures.Phi43.constantsComparison_sunsetLimit N, max (max C₁ C₂) 0,
    min θ₁ θ₂, lt_min hθ₁ hθ₂, fun ε hε => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hC : 0 ≤ max (max C₁ C₂) 0 := le_max_right _ _
  have key : ∀ {Ci θi : ℝ}, Ci ≤ max (max C₁ C₂) 0 → min θ₁ θ₂ ≤ θi →
      Ci * ε ^ θi ≤ max (max C₁ C₂) 0 * ε ^ (min θ₁ θ₂) := by
    intro Ci θi hCi hθi
    calc Ci * ε ^ θi ≤ max (max C₁ C₂) 0 * ε ^ θi :=
          mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg hε0.le _)
      _ ≤ max (max C₁ C₂) 0 * ε ^ (min θ₁ θ₂) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hε0 hε.2 hθi) hC
  exact ⟨(h₁ ε hε).trans (key ((le_max_left _ _).trans (le_max_left _ _)) (min_le_left _ _)),
    (h₂ ε hε).trans (key ((le_max_right _ _).trans (le_max_left _ _)) (min_le_right _ _))⟩

set_option linter.unusedVariables false in
/-- **Convergence of the G-models**, from the existence and uniqueness of the renormalised
canonical model, the Kolmogorov bound for the model norms, the Cauchy property of the noises, the
comparison of the renormalisation constants and the shifted moment inputs. -/
theorem phi43GModels_convergence_of_steps' (hG1 : RenormalisedCanonicalModelStatement)
    (hG5 : KolmogorovModelNormStatement.{u, 0}) (hG7 : NoiseCauchyStatement.{u}) (hG8 : ConstantsComparisonStatement)
    (hin : ∀ (N : ℕ) (κ : RegularityStructures.Phi43.Kappa),
      RegularityStructures.Phi43.ShiftedBphzInputs.{u} N κ) :
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
              (Z ((2 : ℝ) ^ n)⁻¹ ω) (ψ ((2 : ℝ) ^ n)⁻¹ ω) ≤ ENNReal.ofReal B :=
  phi43GModels_convergence_of_steps'_of_shiftRate hG1 hG5 hG7 hG8 hin
    constantDifferencePowerRate_holds

end RegularityStructures.Phi43

end
