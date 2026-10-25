/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Mollifier
public import Phi43.Constants
public import Phi43.ClassicalSolution
public import Phi43.Limit
public import Phi43.Uniqueness
public import Phi43.Preliminaries
public import Phi43.TheoremA.OfKolmogorovModelNorm
public import RegularityStructures.Probability.ModelKolmogorov

/-!
# Proof of Theorem A

The theorem `RegularityStructures.Phi43.theoremA` has exactly the statement
`Statements.theoremA` of Theorem A in `Phi43Statements.TheoremA`. It is
`theoremA_of_kolmogorov_modelNorm` (the deterministic Φ⁴₃ solution map, the convergence of the
BPHZ models, the identification of the renormalised equation, and the maximality and
mollifier-independence arguments) applied to the Kolmogorov criterion for model norms,
`kolmogorov_modelNorm`.
-/

public section

namespace RegularityStructures.Phi43

open MeasureTheory Set
open scoped ENNReal

-- The statement names hypotheses that its own type does not reference.
set_option linter.unusedVariables false in
/-- **Theorem A**: local well-posedness and convergence of the renormalised `Φ⁴₃` equation on `T³`
[Hai14, Theorem 1.15]. -/
theorem theoremA :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (a : ℝ) (u₀ : C(Torus3, ℝ)) (hu₀ : IsSmoothOnTorus u₀)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (ξ : ℝ → Ω → SpaceTime → ℝ) (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : ℝ → Ω → ℝ → C(Torus3, ℝ))
    (hu : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsClassicalSolution
      (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε) (ξ ε ω) u₀ (u ε ω)),
    ∃ (τ : Ω → ℝ≥0∞) (v : Ω → ℝ → HolderBesov η),
      IsPhi43Limit P η u₀ u τ v ∧
      ∀ (ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (ξ' : ℝ → Ω → SpaceTime → ℝ)
        (u' : ℝ → Ω → ℝ → C(Torus3, ℝ)) (τ' : Ω → ℝ≥0∞) (v' : Ω → ℝ → HolderBesov η),
        IsMollifier ρ' →
        (∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ' ε (ξ' ε)) →
        (∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsClassicalSolution
          (a + 3 * wickConstant ρ' ε - 9 * sunsetConstant ρ' ε) (ξ' ε ω) u₀ (u' ε ω)) →
        IsPhi43Limit P η u₀ u' τ' v' →
        τ' =ᵐ[P] τ ∧ ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ENNReal.ofReal t < τ ω → v' ω t = v ω t :=
  theoremA_of_kolmogorov_modelNorm (fun {ι} i1 i2 => @kolmogorov_modelNorm ι i1 i2)

end RegularityStructures.Phi43

end
