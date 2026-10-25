/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentWick
public import Phi43.BPHZ.TreeAllMomentsSetup
public import Phi43.BPHZ.ModelRegPiAllMoments
import Mathlib.Tactic

/-!
# All moments of the recentred convolutions `v₂` and `v₃`

`v₂(x, y) = ∫ δK_{x,y} (Ψ² - c_ε)` and `v₃(x, y) = ∫ δK_{x,y} (Ψ³ - 3 c_ε Ψ)` are tested
polynomial fields of degrees `2` and `3` of the Gaussian field `Ψ`, with the integrable test
function `δK_{x,y}`.  Hence (`integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation`)
for every `p ≥ 1`, `v^(2p)` is integrable and `E v^(2p) ≤ A (E v²)^p` with `A = A(p)` independent
of `N`, `ρ`, `ε`, `x`, `y`, the probability space and the noise.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **All moments of `v₂`**: integrability of the `2p`-th power and moment equivalence. -/
theorem gammaWickSq_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ x y : SpaceTime,
        Integrable (fun ω => gammaWickSq N ρ ε ξ x y ω ^ (2 * p)) P ∧
        ∫ ω, gammaWickSq N ρ ε ξ x y ω ^ (2 * p) ∂P ≤
          A * (∫ ω, gammaWickSq N ρ ε ξ x y ω ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u} 2 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ x y => ?_⟩
  set Q : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε) with hQ
  have hdeg : Q.natDegree ≤ 2 := by rw [hQ]; compute_degree
  have h := hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    (measurable_hairerI2Psi2Kernel N x y) (integrable_hairerI2Psi2Kernel N x y) Q hdeg
  have e : ∀ ω, gammaWickSq N ρ ε ξ x y ω =
      ∫ w, Q.eval (hairerPsiField N ξ ω w) * hairerI2Psi2Kernel N x y w := fun ω => by
    simp only [gammaWickSq, hQ, hairerPsiWickSquare]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp [mul_comm]
  simp only [e]
  exact h

/-- **All moments of `v₃`**: integrability of the `2p`-th power and moment equivalence. -/
theorem gammaWickCube_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ x y : SpaceTime,
        Integrable (fun ω => gammaWickCube N ρ ε ξ x y ω ^ (2 * p)) P ∧
        ∫ ω, gammaWickCube N ρ ε ξ x y ω ^ (2 * p) ∂P ≤
          A * (∫ ω, gammaWickCube N ρ ε ξ x y ω ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u} 3 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ x y => ?_⟩
  set Q : Polynomial ℝ := Polynomial.X ^ 3 -
    Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X with hQ
  have hdeg : Q.natDegree ≤ 3 := by rw [hQ]; compute_degree
  have h := hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    (measurable_hairerI2Psi2Kernel N x y) (integrable_hairerI2Psi2Kernel N x y) Q hdeg
  have e : ∀ ω, gammaWickCube N ρ ε ξ x y ω =
      ∫ w, Q.eval (hairerPsiField N ξ ω w) * hairerI2Psi2Kernel N x y w := fun ω => by
    simp only [gammaWickCube, hQ, hairerPsiWickCube]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp [mul_comm]
  simp only [e]
  exact h

end RegularityStructures.Phi43

end
