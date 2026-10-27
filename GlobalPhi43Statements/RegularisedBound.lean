/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Mollifier
public import Phi43.Constants
public import Phi43.ClassicalSolution
public import RegularityStructures.Torus.HolderBesov
public import RegularityStructures.Probability.WhiteNoise
public import GlobalPhi43.Proofs.RegularisedBound

/-!
# Uniform moment bound for the regularised equations

The moment bound for the classical solutions of the regularised Φ⁴₃ equations on `T³`, uniform in
the regularisation, after Mourrat–Weber, *The dynamic Φ⁴₃ model comes down from infinity* (Commun.
Math. Phys. 356 (2017), (1.27)) and Moinat–Weber, *Space-time localisation for the dynamic Φ⁴₃
model* (Comm. Pure Appl. Math. 73 (2020)). The proof is `GlobalPhi43.regularisedBound`.
-/

public section

namespace GlobalPhi43.Statements

open MeasureTheory Set
open scoped ENNReal NNReal
open RegularityStructures RegularityStructures.Phi43

/-- **Uniform moment bound for the regularised equations.** For `a ∈ ℝ`, `η' ∈ (-2/3, -1/2)` and
a mollifier `ρ` there is a constant profile `C_{a,ρ,η'} : [1, ∞) → [0, ∞)` such that, on every
admissible noise space and for all regularised noises `ξ_ε` driven by its white noise, the classical
solutions `u^a_ε(t,0;x)` from smooth data have `𝓕`-measurable majorants `M_ε ≥ 0` of
`sup_x sup_{0<t≤1} √t ‖u^a_ε(t,0;x)(ω)‖_{η'}`, for every `ω`, with
`sup_ε 𝔼[M_ε^p] ≤ C_{a,ρ,η'}(p)` for every `p ≥ 1`. -/
theorem regularisedBound :
    ∀ (a : ℝ) (η' : ℝ) (hη' : η' ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
      (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ),
    ∃ C : ℝ → ℝ≥0,
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
      (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
      (ξ : ℝ → Ω → SpaceTime → ℝ) (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
      (uε : ℝ → C(Torus3, ℝ) → Ω → ℝ → C(Torus3, ℝ))
      (hu : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ x : C(Torus3, ℝ), IsSmoothOnTorus x → ∀ ω, IsClassicalSolution
        (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε) (ξ ε ω) x (uε ε x ω)),
    ∃ M : ℝ → Ω → ℝ,
      (∀ ε ∈ Ioc (0 : ℝ) 1, Measurable (M ε) ∧ ∀ ω, 0 ≤ M ε ω) ∧
      (∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, ∀ x : C(Torus3, ℝ), IsSmoothOnTorus x → ∀ t ∈ Ioc (0 : ℝ) 1,
        ENNReal.ofReal (√t) * holderBesovENorm η' (uε ε x ω t) ≤ ENNReal.ofReal (M ε ω)) ∧
      ∀ p : ℝ, 1 ≤ p →
        ⨆ ε ∈ Ioc (0 : ℝ) 1, ∫⁻ ω, ENNReal.ofReal (M ε ω) ^ p ∂P ≤ C p :=
  by exact GlobalPhi43.regularisedBound

end GlobalPhi43.Statements

end
