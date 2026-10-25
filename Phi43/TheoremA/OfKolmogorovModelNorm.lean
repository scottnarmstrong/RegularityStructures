/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.OfSteps
public import Phi43.TheoremA.GModelsConvergenceOfKolmogorov
public import Phi43.Steps.ClassicalSolutionStoppedContinuity

/-!
# Theorem A from the Kolmogorov criterion for model norms

`theoremA_of_kolmogorov_modelNorm` proves the statement of Theorem A (conclusion as in
`theoremA_of_steps`) from the Kolmogorov criterion for model norms alone
(`KolmogorovModelNormStatement`, the statement of `kolmogorov_modelNorm`). It applies
`theoremA_of_steps` to the existence and uniqueness of the renormalised canonical model
(`renormalisedCanonicalModel_existsUnique`), the persistence and stopped continuity of classical
solutions (`phi43ClassicalSolution_stoppedContinuity`), the convergence of the noise potentials
(`phi43Noise_cauchy`), and the convergence of the G-models, obtained from the Kolmogorov criterion
by `phi43GModels_convergence_of_kolmogorov_modelNorm`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

universe u

/-- **Theorem A from the Kolmogorov criterion for model norms.** -/
theorem theoremA_of_kolmogorov_modelNorm (hG5 : Phi43.KolmogorovModelNormStatement.{u, 0}) :
    ∀ {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (SpaceTime → ℝ) → Ω → ℝ)
      (_hW : IsWhiteNoise P W) (a : ℝ)
      (u₀ : C(Torus3, ℝ)) (_hu₀ : IsSmoothOnTorus u₀)
      (η : NegExponent)
      (_hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
      (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_hρ : IsMollifier ρ)
      (ξ : ℝ → Ω → SpaceTime → ℝ)
      (_hξ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        IsRegularisedNoise P W ρ ε (ξ ε))
      (u : ℝ → Ω → ℝ → C(Torus3, ℝ))
      (_hu : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ω,
        IsClassicalSolution
          (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε)
          (ξ ε ω) u₀ (u ε ω)),
      ∃ (τ : Ω → ℝ≥0∞) (v : Ω → ℝ → HolderBesov η),
        IsPhi43Limit P η u₀ u τ v ∧
        ∀ (ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
          (ξ' : ℝ → Ω → SpaceTime → ℝ)
          (u' : ℝ → Ω → ℝ → C(Torus3, ℝ))
          (τ' : Ω → ℝ≥0∞) (v' : Ω → ℝ → HolderBesov η),
          IsMollifier ρ' →
          (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
            IsRegularisedNoise P W ρ' ε (ξ' ε)) →
          (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ω,
            IsClassicalSolution
              (a + 3 * wickConstant ρ' ε - 9 * sunsetConstant ρ' ε)
              (ξ' ε ω) u₀ (u' ε ω)) →
          IsPhi43Limit P η u₀ u' τ' v' →
          τ' =ᵐ[P] τ ∧ ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
            ENNReal.ofReal t < τ ω → v' ω t = v ω t := by
  have hG1 : Phi43.RenormalisedCanonicalModelStatement := fun N κ noise Cg q hg C =>
    renormalisedCanonicalModel_existsUnique N κ noise Cg q hg C
  have hG4 := phi43ClassicalSolution_stoppedContinuity
  have hG7 : Phi43.NoiseCauchyStatement.{u} := phi43Noise_cauchy
  apply theoremA_of_steps hG1 hG4 hG7
  exact phi43GModels_convergence_of_kolmogorov_modelNorm hG5

end RegularityStructures.Phi43

end
