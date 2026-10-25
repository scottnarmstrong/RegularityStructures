/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiFieldMoment
public import Phi43.BPHZ.ModelRegPiTreesMoments

/-!
# All moments of the tested field of `I(Ψ²)Ψ`, with integrability

The field `I₂Ψ_x(y) = (∫ (K(y - w) - K(x - w)) :Ψ²:(w) dw) Ψ(y)` is of the form
`(∫ A(y, w) P₁(Ψ(w)) dw) P₂(Ψ(y)) + P₃(Ψ(y))` with `P₁ = X² - c`, `P₂ = X`, `P₃ = 0`, so the chaos
moment equivalence (`integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation`) gives
all moments of the semigroup-tested field from the second moment.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **All moments of the tested field of `I(Ψ²)Ψ`, semigroup test, with integrability.** -/
theorem productISqPsiField_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ (x : SpaceTime) (z : ParabolicSpace),
        Integrable (fun ω => (∫ w, productISqPsiField N ρ ε ξ x ω w *
          semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, productISqPsiField N ρ ε ξ x ω w * semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, productISqPsiField N ρ ε ξ x ω w * semigroupPeriodised t z w) ^ 2
            ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation.{u} 5 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ {t} ht x z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  have key := fun (P₁ P₂ P₃ : Polynomial ℝ) (hd12 : P₁.natDegree + P₂.natDegree ≤ 5)
      (hd3 : P₃.natDegree ≤ 5) =>
    hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    hgm hgi (measurable_uncurry_hairerI2Psi2Kernel N x) (integrable_hairerI2Psi2Kernel N x)
    (fun y => integral_abs_hairerKernelTorus_diff_le N x y)
    (hairerI2Psi2Kernel_slab_support N x) P₁ P₂ P₃ hd12 hd3
  set Q : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε) with hQ
  have hd1 : Q.natDegree ≤ 2 := by rw [hQ]; compute_degree
  have h := key Q Polynomial.X 0 (by
      rw [Polynomial.natDegree_X]; omega) (by simp)
  have e : ∀ ω, ∫ w, productISqPsiField N ρ ε ξ x ω w * semigroupPeriodised t z w =
      ∫ y, ((∫ w, hairerI2Psi2Kernel N x y w * Q.eval (hairerPsiField N ξ ω w)) *
        (Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω y) +
          (0 : Polynomial ℝ).eval (hairerPsiField N ξ ω y)) *
        semigroupPeriodised t z y := fun ω => by
    simp [hQ, productISqPsiField, hairerPsiWickSquare]
  simp only [e]
  exact h

end RegularityStructures.Phi43

end
