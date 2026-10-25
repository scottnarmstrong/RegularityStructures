/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GModelsConvergenceDyadic
public import Phi43.BPHZ.GModelsConstantShift
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Dist
public import Phi43Statements.Defs.Phi43Size

/-!
# Convergence of the G-models, given a power rate for the constant differences

The conclusion of `phi43GModels_convergence_of_steps'_of_shiftRate` is exactly the statement of
the convergence of the G-models (`Statements.phi43GModels_convergence`, all parameters universally
quantified, universe `u` for the probability space).  Its hypotheses are the existence and
uniqueness of the renormalised canonical model, the Kolmogorov bound for the model norms, the
Cauchy property of the noises, the comparison of the renormalisation constants, the shifted moment
inputs, and a power rate `hrateAll` for the convergence of the constant differences.

The argument does not use a Lipschitz bound for the action of the renormalisation constants on
models: the shifted BPHZ models with constants `C_K(ρ, ε) + c` are shown to be Cauchy directly,
uniformly in the shift `c`.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

universe u

namespace RegularityStructures.Phi43

/-- A power rate for the constant differences (the limits being those of the comparison of the
renormalisation constants), for every `N` and every mollifier. -/
@[expose] def ConstantDifferencePowerRate : Prop :=
  ∀ (N : ℕ) (ρ : RegularityStructures.ParabolicSpace → ℝ),
    RegularityStructures.Phi43.IsMollifier ρ →
    ∃ L₁ L₂ C θ' : ℝ, 0 < θ' ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      |RegularityStructures.Phi43.wickConstant ρ ε -
          RegularityStructures.Phi43.hairerWickConstant N ρ ε - L₁| ≤ C * ε ^ θ' ∧
      |RegularityStructures.Phi43.sunsetConstant ρ ε -
          RegularityStructures.Phi43.hairerSunsetConstant N ρ ε - L₂| ≤ C * ε ^ θ'

/-- The rate for the constant differences gives the rate for the shifts `gModelsShift N ρ c`. -/
theorem gModelsShift_rate_of_constantDifferencePowerRate (h : ConstantDifferencePowerRate) (N : ℕ)
    {ρ : RegularityStructures.ParabolicSpace → ℝ} (hρ : RegularityStructures.Phi43.IsMollifier ρ)
    (c : RegularityStructures.Phi43.RenormalisationConstants) :
    ∃ L : RegularityStructures.Phi43.RenormalisationConstants, ∃ C θ' : ℝ, 0 < θ' ∧
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        ‖RegularityStructures.Phi43.gModelsShift N ρ c ε - L‖ ≤ C * ε ^ θ' := by
  obtain ⟨L₁, L₂, C, θ', hθ', hr⟩ := h N ρ hρ
  refine ⟨(L₁ + c.1, L₂ + c.2), C, θ', hθ', fun ε hε => ?_⟩
  obtain ⟨h1, h2⟩ := hr ε hε
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · have e : (RegularityStructures.Phi43.gModelsShift N ρ c ε - (L₁ + c.1, L₂ + c.2)).1 =
        RegularityStructures.Phi43.wickConstant ρ ε -
          RegularityStructures.Phi43.hairerWickConstant N ρ ε - L₁ := by
      simp only [RegularityStructures.Phi43.gModelsShift, Prod.fst_sub]; ring
    rw [e, Real.norm_eq_abs]; exact h1
  · have e : (RegularityStructures.Phi43.gModelsShift N ρ c ε - (L₁ + c.1, L₂ + c.2)).2 =
        RegularityStructures.Phi43.sunsetConstant ρ ε -
          RegularityStructures.Phi43.hairerSunsetConstant N ρ ε - L₂ := by
      simp only [RegularityStructures.Phi43.gModelsShift, Prod.snd_sub]; ring
    rw [e, Real.norm_eq_abs]; exact h2

set_option linter.unusedVariables false in
/-- **Convergence of the G-models, given a power rate for the constant differences.** -/
theorem phi43GModels_convergence_of_steps'_of_shiftRate (hG1 : RenormalisedCanonicalModelStatement)
    (hG5 : KolmogorovModelNormStatement.{u, 0}) (hG7 : NoiseCauchyStatement.{u}) (hG8 : ConstantsComparisonStatement)
    (hin : ∀ (N : ℕ) (κ : RegularityStructures.Phi43.Kappa),
      RegularityStructures.Phi43.ShiftedBphzInputs.{u} N κ)
    (hrateAll : ConstantDifferencePowerRate) :
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
  intro κ hκE N hN η hη hκη ρ ρ' hρ hρ' c Ω _ P _ W hW ξ ξ' hξ hξ' Z Z' ψ ψ' hlift hlift'
  refine ⟨gModels_tight hG1 hG5 hG7 hG8 hin hκE hN hη hρ c P W hW ξ hξ Z ψ hlift,
    gModels_cauchy hG1 hG5 hG7 hG8 hin hκE hN hη hρ hρ' c P W hW ξ ξ' hξ hξ' Z Z' ψ ψ'
      hlift hlift', ?_⟩
  refine ae_all_iff.2 fun T => ?_
  by_cases hT : 1 ≤ T
  · have hT' : (1 : ℝ) ≤ (T : ℝ) := Nat.one_le_cast.2 hT
    have := gModels_dyadic_of_shiftRate hG1 hG5 hG7 hG8 hin hκE hN hη hρ c
      (gModelsShift_rate_of_constantDifferencePowerRate hrateAll N hρ c) P W hW ξ hξ Z ψ hlift
      (T : ℝ) hT'
    filter_upwards [this] with ω hω _
    simpa only [inv_pow] using hω
  · exact Filter.Eventually.of_forall fun ω h => absurd h hT

end RegularityStructures.Phi43

end
