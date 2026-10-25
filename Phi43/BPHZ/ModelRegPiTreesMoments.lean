/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiAllMoments
public import Phi43.BPHZ.SemigroupTestAllMoments
public import Phi43.BPHZ.TreeI3Psi2Field

/-!
# All moments of the tested tree fields, with integrability

For the noise `Ξ`, the Wick powers `:Ψ²:`, `:Ψ³:` and the fields of `I(Ψ³)Ψ`, `I(Ψ²)Ψ²`,
`I(Ψ³)Ψ²`, tested against the periodised semigroup kernel `q^♯_t(x, ·)`: the `2p`-th moment is
bounded by a constant times the `p`-th power of the second moment, and the `2p`-th power of the
tested field is integrable (`regularisedNoise_semigroupPeriodised_integrable_pow_le`,
`hairerPsiWickSquare_semigroupPeriodised_integrable_pow_le`, …,
`hairerI3Psi2Field_semigroupPeriodised_integrable_pow_le`). The bounds are stated without
absolute values, in the form used by `lintegral_enorm_pow_le_of_moments`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **All moments of the tested noise `Ξ`, semigroup test, with integrability.** -/
theorem regularisedNoise_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ}, IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ z : ParabolicSpace,
        Integrable (fun ω => (∫ w, ξ ω w * semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, ξ ω w * semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, ξ ω w * semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u} 1 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} hρ hW hε hξ {t} ht z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  have h := hA hW (fun ω => IsSmoothOnSpaceTime.continuous (hξ.1 ω)) (fun y => (hξ.2 y).1)
    (exists_regularisedNoise_pairing hρ hε hξ)
    (fun y => integral_regularisedNoise_sq_le hρ hε hW hξ y) hgm hgi Polynomial.X
    (by simp)
  simpa only [Polynomial.eval_X] using h

/-- **All moments of the tested Wick square of `Ψ`, semigroup test, with integrability.** -/
theorem hairerPsiWickSquare_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ z : ParabolicSpace,
        Integrable (fun ω => (∫ w, hairerPsiWickSquare N ρ ε ξ ω w * semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, hairerPsiWickSquare N ρ ε ξ ω w * semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, hairerPsiWickSquare N ρ ε ξ ω w * semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u} 2 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ {t} ht z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  set Q : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε) with hQ
  have hdeg : Q.natDegree ≤ 2 := by rw [hQ]; compute_degree
  have h := hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    hgm hgi Q hdeg
  have e : ∀ ω, ∫ w, hairerPsiWickSquare N ρ ε ξ ω w * semigroupPeriodised t z w =
      ∫ y, Q.eval (hairerPsiField N ξ ω y) * semigroupPeriodised t z y := fun ω => by
    simp [hQ, hairerPsiWickSquare]
  simp only [e]
  exact h

/-- **All moments of the tested Wick cube of `Ψ`, semigroup test, with integrability.** -/
theorem hairerPsiWickCube_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ z : ParabolicSpace,
        Integrable (fun ω => (∫ w, hairerPsiWickCube N ρ ε ξ ω w * semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, hairerPsiWickCube N ρ ε ξ ω w * semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, hairerPsiWickCube N ρ ε ξ ω w * semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u} 3 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ {t} ht z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  set Q : Polynomial ℝ := Polynomial.X ^ 3 -
    Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X with hQ
  have hdeg : Q.natDegree ≤ 3 := by rw [hQ]; compute_degree
  have h := hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    hgm hgi Q hdeg
  have e : ∀ ω, ∫ w, hairerPsiWickCube N ρ ε ξ ω w * semigroupPeriodised t z w =
      ∫ y, Q.eval (hairerPsiField N ξ ω y) * semigroupPeriodised t z y := fun ω => by
    simp [hQ, hairerPsiWickCube]
  simp only [e]
  exact h

/-- **All moments of the tested field of `I₃Ψ`, semigroup test, with integrability.** -/
theorem hairerI3PsiField_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ (x : SpaceTime) (z : ParabolicSpace),
        Integrable (fun ω => (∫ w, hairerI3PsiField N ρ ε ξ x ω w * semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, hairerI3PsiField N ρ ε ξ x ω w * semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, hairerI3PsiField N ρ ε ξ x ω w * semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation.{u} 5 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ {t} ht x z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  have key := fun (P₁ P₂ P₃ : Polynomial ℝ) (hd12 : P₁.natDegree + P₂.natDegree ≤ 5)
      (hd3 : P₃.natDegree ≤ 5) =>
    hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    hgm hgi (measurable_uncurry_hairerI2Psi2Kernel N x) (integrable_hairerI2Psi2Kernel N x)
    (fun y => integral_abs_hairerKernelTorus_diff_le N x y)
    (hairerI2Psi2Kernel_slab_support N x) P₁ P₂ P₃ hd12 hd3
  set P₁ : Polynomial ℝ := Polynomial.X ^ 3 -
    Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X with hP₁
  have hd1 : P₁.natDegree ≤ 3 := by rw [hP₁]; compute_degree
  have h := key P₁ Polynomial.X 0 (by
      rw [Polynomial.natDegree_X]; omega) (by simp)
  have e : ∀ ω, ∫ w, hairerI3PsiField N ρ ε ξ x ω w * semigroupPeriodised t z w =
      ∫ y, ((∫ w, hairerI2Psi2Kernel N x y w * P₁.eval (hairerPsiField N ξ ω w)) *
        (Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω y) +
          (0 : Polynomial ℝ).eval (hairerPsiField N ξ ω y)) *
        semigroupPeriodised t z y := fun ω => by
    simp [hP₁, hairerI3PsiField, hairerPsiWickCubeField, hairerI2Psi2Kernel]
  simp only [e]
  exact h

/-- **All moments of the tested field of `I(Ψ²)Ψ²`, semigroup test, with integrability.** -/
theorem hairerI2Psi2Field_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ (x : SpaceTime) (z : ParabolicSpace),
        Integrable (fun ω => (∫ w, hairerI2Psi2Field N ρ ε ξ x ω w * semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, hairerI2Psi2Field N ρ ε ξ x ω w * semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, hairerI2Psi2Field N ρ ε ξ x ω w * semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation.{u} 5 p hp
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
  set P₃ : Polynomial ℝ := Polynomial.C (-hairerSunsetConstant N ρ ε) with hP₃
  have hd1 : Q.natDegree ≤ 2 := by rw [hQ]; compute_degree
  have h := key Q Q P₃ (by omega) (by rw [hP₃]; simp)
  have e : ∀ ω, ∫ w, hairerI2Psi2Field N ρ ε ξ x ω w * semigroupPeriodised t z w =
      ∫ y, ((∫ w, hairerI2Psi2Kernel N x y w * Q.eval (hairerPsiField N ξ ω w)) *
        Q.eval (hairerPsiField N ξ ω y) + P₃.eval (hairerPsiField N ξ ω y)) *
        semigroupPeriodised t z y := fun ω => by
    simp [hQ, hP₃, hairerI2Psi2Field, hairerPsiWickSquare, sub_eq_add_neg]
  simp only [e]
  exact h

/-- **All moments of the tested field of `I(Ψ³)Ψ²`, semigroup test, with integrability.** -/
theorem hairerI3Psi2Field_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ (x : SpaceTime) (z : ParabolicSpace),
        Integrable (fun ω => (∫ w, hairerI3Psi2Field N ρ ε ξ x ω w * semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, hairerI3Psi2Field N ρ ε ξ x ω w * semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, hairerI3Psi2Field N ρ ε ξ x ω w * semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation.{u} 5 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ {t} ht x z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  have key := fun (P₁ P₂ P₃ : Polynomial ℝ) (hd12 : P₁.natDegree + P₂.natDegree ≤ 5)
      (hd3 : P₃.natDegree ≤ 5) =>
    hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    hgm hgi (measurable_uncurry_hairerI2Psi2Kernel N x) (integrable_hairerI2Psi2Kernel N x)
    (fun y => integral_abs_hairerKernelTorus_diff_le N x y)
    (hairerI2Psi2Kernel_slab_support N x) P₁ P₂ P₃ hd12 hd3
  set P₁ : Polynomial ℝ := Polynomial.X ^ 3 -
    Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X with hP₁
  set P₂ : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε) with hP₂
  set P₃ : Polynomial ℝ :=
    Polynomial.C (-(3 * hairerSunsetConstant N ρ ε)) * Polynomial.X with hP₃
  have hd1 : P₁.natDegree ≤ 3 := by rw [hP₁]; compute_degree
  have hd2 : P₂.natDegree ≤ 2 := by rw [hP₂]; compute_degree
  have hd3 : P₃.natDegree ≤ 1 := by rw [hP₃]; compute_degree
  have h := key P₁ P₂ P₃ (by omega) (hd3.trans (by norm_num))
  have e : ∀ ω, ∫ w, hairerI3Psi2Field N ρ ε ξ x ω w * semigroupPeriodised t z w =
      ∫ y, ((∫ w, hairerI2Psi2Kernel N x y w * P₁.eval (hairerPsiField N ξ ω w)) *
        P₂.eval (hairerPsiField N ξ ω y) + P₃.eval (hairerPsiField N ξ ω y)) *
        semigroupPeriodised t z y := fun ω => by
    simp [hP₁, hP₂, hP₃, hairerI3Psi2Field, hairerPsiWickCube, hairerPsiWickSquare,
      sub_eq_add_neg]
  simp only [e]
  exact h

end RegularityStructures.Phi43

end
