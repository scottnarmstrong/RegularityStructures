/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiFieldMoment
public import Phi43.BPHZ.SemigroupTestAllMomentsSetup
public import RegularityStructures.BPHZ.ChaosLimitMomentsTwoFieldsKernelTruncation

/-!
# All moments of the tested two-mollifier difference of `I(Ψ²)Ψ`, with integrability

The field `I₂Ψ` has the form `(∫ k(y, w) P₁(Ψ(w)) dw) P₂(Ψ(y)) + P₃(Ψ(y))` with
`P₁ = X² - c`, `P₂ = X`, `P₃ = 0`, so
`integrable_and_integral_pow_two_mul_le_of_chaosField_sub_timeTruncation` applies to the difference
of two such fields.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **All moments of the tested two-mollifier difference of `I₂Ψ`, semigroup test.** -/
theorem productISqPsiField_sub_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → ∀ (x : SpaceTime) (z : ParabolicSpace),
        Integrable (fun ω => (∫ w, (productISqPsiField N ρ ε ξ x ω w -
          productISqPsiField N ρ' ε' ξ' x ω w) * semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, (productISqPsiField N ρ ε ξ x ω w - productISqPsiField N ρ' ε' ξ' x ω w) *
            semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, (productISqPsiField N ρ ε ξ x ω w -
            productISqPsiField N ρ' ε' ξ' x ω w) * semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_chaosField_sub_timeTruncation.{u} 5 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' {t} ht x z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  have hdeg : ∀ c : ℝ, (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℝ).natDegree ≤ 2 :=
    fun c => by compute_degree
  have h := hA hW (continuous_hairerPsiField N hξ.1) (continuous_hairerPsiField N hξ'.1)
    (measurable_hairerPsiField_apply N hξ) (measurable_hairerPsiField_apply N hξ')
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (exists_hairerPsiField_pairing N hρ' hε' hW hξ')
    (V := max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0))
    (fun z => (integral_hairerPsiField_sq_le N hρ hε hW hξ z).trans (le_max_left _ _))
    (fun z => (integral_hairerPsiField_sq_le N hρ' hε' hW hξ' z).trans (le_max_right _ _))
    hgm hgi (measurable_uncurry_hairerI2Psi2Kernel N x) (integrable_hairerI2Psi2Kernel N x)
    (fun y => integral_abs_hairerKernelTorus_diff_le N x y)
    (hairerI2Psi2Kernel_slab_support N x)
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε)) Polynomial.X 0
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ' ε')) Polynomial.X 0
    (by have := hdeg (hairerWickConstant N ρ ε); rw [Polynomial.natDegree_X]; omega) (by simp)
    (by have := hdeg (hairerWickConstant N ρ' ε'); rw [Polynomial.natDegree_X]; omega) (by simp)
  have e : ∀ (ρ₀ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ : ℝ) (ξ₀ : Ω → SpaceTime → ℝ) (ω : Ω) (w : SpaceTime),
      productISqPsiField N ρ₀ ε₀ ξ₀ x ω w = chaosField (hairerPsiField N ξ₀)
        (hairerI2Psi2Kernel N x) (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ₀ ε₀))
        Polynomial.X 0 ω w :=
    fun ρ₀ ε₀ ξ₀ ω w => by
      simp [chaosField, productISqPsiField, hairerPsiWickSquare]
  simp only [e]
  exact h

end RegularityStructures.Phi43

end
