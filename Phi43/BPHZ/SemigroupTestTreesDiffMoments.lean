/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestAllMomentsSetup
public import Phi43.BPHZ.TreeWickCube
public import Phi43.BPHZ.TreeI3PsiField
public import Phi43.BPHZ.TreeI3Psi2Field
public import RegularityStructures.BPHZ.ChaosLimitMomentsTwoFieldsKernelTruncation

/-!
# All moments of the tested cross-mollifier differences of the `I`-trees, with integrability

For regularised noises `ξ` (mollifier `ρ`, scale `ε`), `ξ'` (mollifier `ρ'`, scale `ε'`) of the same
white noise, a base point `x`, `p ≥ 1` and `τ ∈ {I(Ψ³)Ψ, I(Ψ²)Ψ², I(Ψ³)Ψ²}`, the tested difference
`X = ∫ (F_τ - F'_τ) q^♯_t(z, ·)` has integrable `2p`-th power and `E X^(2p) ≤ A (E X²)^p` with
`A = A(p)` independent of everything else.  Each field has the form
`(∫ k(y, w) P₁(Ψ(w)) dw) P₂(Ψ(y)) + P₃(Ψ(y))` of total degree at most `5`
(`chaosField`), so `integrable_and_integral_pow_two_mul_le_of_chaosField_sub_timeTruncation`
applies.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **All moments of the tested cross-mollifier difference of the field of `I₃Ψ`, semigroup
test.** -/
theorem hairerI3PsiField_sub_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → ∀ (x : SpaceTime) (z : ParabolicSpace),
        Integrable (fun ω => (∫ w, (hairerI3PsiField N ρ ε ξ x ω w -
          hairerI3PsiField N ρ' ε' ξ' x ω w) * semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, (hairerI3PsiField N ρ ε ξ x ω w - hairerI3PsiField N ρ' ε' ξ' x ω w) *
            semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, (hairerI3PsiField N ρ ε ξ x ω w - hairerI3PsiField N ρ' ε' ξ' x ω w) *
            semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_chaosField_sub_timeTruncation.{u} 5 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' {t} ht x z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  set P₁ : Polynomial ℝ := Polynomial.X ^ 3 -
    Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X with hP₁
  set P₁' : Polynomial ℝ := Polynomial.X ^ 3 -
    Polynomial.C (3 * hairerWickConstant N ρ' ε') * Polynomial.X with hP₁'
  have hd1 : P₁.natDegree ≤ 3 := by rw [hP₁]; compute_degree
  have hd1' : P₁'.natDegree ≤ 3 := by rw [hP₁']; compute_degree
  have h := hA hW (continuous_hairerPsiField N hξ.1) (continuous_hairerPsiField N hξ'.1)
    (measurable_hairerPsiField_apply N hξ) (measurable_hairerPsiField_apply N hξ')
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (exists_hairerPsiField_pairing N hρ' hε' hW hξ')
    (V := max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0))
    (fun z => (integral_hairerPsiField_sq_le N hρ hε hW hξ z).trans (le_max_left _ _))
    (fun z => (integral_hairerPsiField_sq_le N hρ' hε' hW hξ' z).trans (le_max_right _ _))
    hgm hgi (measurable_uncurry_hairerI2Psi2Kernel N x) (integrable_hairerI2Psi2Kernel N x)
    (fun y => integral_abs_hairerKernelTorus_diff_le N x y)
    (hairerI2Psi2Kernel_slab_support N x) P₁ Polynomial.X 0 P₁' Polynomial.X 0
    (by rw [Polynomial.natDegree_X]; omega) (by simp)
    (by rw [Polynomial.natDegree_X]; omega) (by simp)
  have e : ∀ (ρ₀ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ : ℝ) (ξ₀ : Ω → SpaceTime → ℝ) (ω : Ω) (w : SpaceTime),
      hairerI3PsiField N ρ₀ ε₀ ξ₀ x ω w = chaosField (hairerPsiField N ξ₀)
        (hairerI2Psi2Kernel N x) (Polynomial.X ^ 3 -
          Polynomial.C (3 * hairerWickConstant N ρ₀ ε₀) * Polynomial.X) Polynomial.X 0 ω w :=
    fun ρ₀ ε₀ ξ₀ ω w => by
      simp [chaosField, hairerI3PsiField, hairerPsiWickCubeField, hairerI2Psi2Kernel]
  simp only [e]
  exact h

/-- **All moments of the tested cross-mollifier difference of the field of `I(Ψ²)Ψ²`, semigroup
test.** -/
theorem hairerI2Psi2Field_sub_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → ∀ (x : SpaceTime) (z : ParabolicSpace),
        Integrable (fun ω => (∫ w, (hairerI2Psi2Field N ρ ε ξ x ω w -
          hairerI2Psi2Field N ρ' ε' ξ' x ω w) * semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, (hairerI2Psi2Field N ρ ε ξ x ω w - hairerI2Psi2Field N ρ' ε' ξ' x ω w) *
            semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, (hairerI2Psi2Field N ρ ε ξ x ω w - hairerI2Psi2Field N ρ' ε' ξ' x ω w) *
            semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
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
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε))
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε))
    (Polynomial.C (-hairerSunsetConstant N ρ ε))
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ' ε'))
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ' ε'))
    (Polynomial.C (-hairerSunsetConstant N ρ' ε'))
    (by have := hdeg (hairerWickConstant N ρ ε); omega) (by simp)
    (by have := hdeg (hairerWickConstant N ρ' ε'); omega) (by simp)
  have e : ∀ (ρ₀ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ : ℝ) (ξ₀ : Ω → SpaceTime → ℝ) (ω : Ω) (w : SpaceTime),
      hairerI2Psi2Field N ρ₀ ε₀ ξ₀ x ω w = chaosField (hairerPsiField N ξ₀)
        (hairerI2Psi2Kernel N x) (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ₀ ε₀))
        (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ₀ ε₀))
        (Polynomial.C (-hairerSunsetConstant N ρ₀ ε₀)) ω w :=
    fun ρ₀ ε₀ ξ₀ ω w => by
      simp [chaosField, hairerI2Psi2Field, hairerPsiWickSquare, sub_eq_add_neg]
  simp only [e]
  exact h

/-- **All moments of the tested cross-mollifier difference of the field of `I(Ψ³)Ψ²`, semigroup
test.** -/
theorem hairerI3Psi2Field_sub_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → ∀ (x : SpaceTime) (z : ParabolicSpace),
        Integrable (fun ω => (∫ w, (hairerI3Psi2Field N ρ ε ξ x ω w -
          hairerI3Psi2Field N ρ' ε' ξ' x ω w) * semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, (hairerI3Psi2Field N ρ ε ξ x ω w - hairerI3Psi2Field N ρ' ε' ξ' x ω w) *
            semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, (hairerI3Psi2Field N ρ ε ξ x ω w - hairerI3Psi2Field N ρ' ε' ξ' x ω w) *
            semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_chaosField_sub_timeTruncation.{u} 5 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' {t} ht x z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  have hd1 : ∀ c : ℝ, (Polynomial.X ^ 3 - Polynomial.C (3 * c) * Polynomial.X :
      Polynomial ℝ).natDegree ≤ 3 := fun c => by compute_degree
  have hd2 : ∀ c : ℝ, (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℝ).natDegree ≤ 2 :=
    fun c => by compute_degree
  have hd3 : ∀ c : ℝ, (Polynomial.C (-(3 * c)) * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 :=
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
    (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X)
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε))
    (Polynomial.C (-(3 * hairerSunsetConstant N ρ ε)) * Polynomial.X)
    (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ' ε') * Polynomial.X)
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ' ε'))
    (Polynomial.C (-(3 * hairerSunsetConstant N ρ' ε')) * Polynomial.X)
    (by have := hd1 (hairerWickConstant N ρ ε); have := hd2 (hairerWickConstant N ρ ε); omega)
    ((hd3 _).trans (by norm_num))
    (by have := hd1 (hairerWickConstant N ρ' ε'); have := hd2 (hairerWickConstant N ρ' ε'); omega)
    ((hd3 _).trans (by norm_num))
  have e : ∀ (ρ₀ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ : ℝ) (ξ₀ : Ω → SpaceTime → ℝ) (ω : Ω) (w : SpaceTime),
      hairerI3Psi2Field N ρ₀ ε₀ ξ₀ x ω w = chaosField (hairerPsiField N ξ₀)
        (hairerI2Psi2Kernel N x)
        (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ₀ ε₀) * Polynomial.X)
        (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ₀ ε₀))
        (Polynomial.C (-(3 * hairerSunsetConstant N ρ₀ ε₀)) * Polynomial.X) ω w :=
    fun ρ₀ ε₀ ξ₀ ω w => by
      simp [chaosField, hairerI3Psi2Field, hairerPsiWickCube, hairerPsiWickSquare,
        sub_eq_add_neg]
  simp only [e]
  exact h

end RegularityStructures.Phi43

end
