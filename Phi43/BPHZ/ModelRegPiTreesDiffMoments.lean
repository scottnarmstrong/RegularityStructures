/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestDiffMoments
public import Phi43.BPHZ.SemigroupTestAllMomentsSetup
public import Phi43.BPHZ.SemigroupTestAllMoments
public import Phi43.BPHZ.TreeWickCube
public import Phi43.BPHZ.TreeWickSquare

/-!
# All moments of the tested cross-mollifier differences of `Ψ`, `:Ψ²:`, `:Ψ³:`, with integrability

For regularised noises `ξ` (mollifier `ρ`, scale `ε`), `ξ'` (mollifier `ρ'`, scale `ε'`) of the same
white noise and `p ≥ 1`, the tested difference `X = ∫ (F_ε - F_ε') q^♯_t(z, ·)` has integrable
`2p`-th power and `E X^(2p) ≤ A (E X²)^p` with `A = A(p)` independent of everything else.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **All moments of the tested cross-mollifier difference of `Ψ`, semigroup test.** -/
theorem hairerPsiField_sub_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → ∀ z : ParabolicSpace,
        Integrable (fun ω => (∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) *
          semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) *
            semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) *
            semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub_timeTruncation.{u} 1 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' {t} ht z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  have hd : (Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by simp
  have hd' := hd
  have h := hA hW (continuous_hairerPsiField N hξ.1) (continuous_hairerPsiField N hξ'.1)
    (measurable_hairerPsiField_apply N hξ) (measurable_hairerPsiField_apply N hξ')
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (exists_hairerPsiField_pairing N hρ' hε' hW hξ')
    (V := max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0))
    (fun z => (integral_hairerPsiField_sq_le N hρ hε hW hξ z).trans (le_max_left _ _))
    (fun z => (integral_hairerPsiField_sq_le N hρ' hε' hW hξ' z).trans (le_max_right _ _))
    hgm hgi Polynomial.X Polynomial.X hd hd'
  have e : ∀ ω, ∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) * semigroupPeriodised t z w =
      ∫ y, (Polynomial.X.eval (hairerPsiField N ξ ω y) - Polynomial.X.eval (hairerPsiField N ξ' ω y)) *
        semigroupPeriodised t z y := fun ω => by
    simp
  simp only [e]
  exact h

/-- **All moments of the tested cross-mollifier difference of `:Ψ²:`, semigroup test.** -/
theorem hairerPsiWickSquare_sub_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → ∀ z : ParabolicSpace,
        Integrable (fun ω => (∫ w, (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w) *
          semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w) *
            semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w) *
            semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub_timeTruncation.{u} 2 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' {t} ht z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  have hdeg : ∀ c : ℝ, (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℝ).natDegree ≤ 2 :=
    fun c => by compute_degree
  have hd := hdeg (hairerWickConstant N ρ ε)
  have hd' := hdeg (hairerWickConstant N ρ' ε')
  have h := hA hW (continuous_hairerPsiField N hξ.1) (continuous_hairerPsiField N hξ'.1)
    (measurable_hairerPsiField_apply N hξ) (measurable_hairerPsiField_apply N hξ')
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (exists_hairerPsiField_pairing N hρ' hε' hW hξ')
    (V := max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0))
    (fun z => (integral_hairerPsiField_sq_le N hρ hε hW hξ z).trans (le_max_left _ _))
    (fun z => (integral_hairerPsiField_sq_le N hρ' hε' hW hξ' z).trans (le_max_right _ _))
    hgm hgi (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε)) (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ' ε')) hd hd'
  have e : ∀ ω, ∫ w, (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w) * semigroupPeriodised t z w =
      ∫ y, ((Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε)).eval (hairerPsiField N ξ ω y) - (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ' ε')).eval (hairerPsiField N ξ' ω y)) *
        semigroupPeriodised t z y := fun ω => by
    simp [hairerPsiWickSquare]
  simp only [e]
  exact h

/-- **All moments of the tested cross-mollifier difference of `:Ψ³:`, semigroup test.** -/
theorem hairerPsiWickCube_sub_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → ∀ z : ParabolicSpace,
        Integrable (fun ω => (∫ w, (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w) *
          semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w) *
            semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w) *
            semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub_timeTruncation.{u} 3 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' {t} ht z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  have hdeg : ∀ c : ℝ, (Polynomial.X ^ 3 - Polynomial.C (3 * c) * Polynomial.X :
      Polynomial ℝ).natDegree ≤ 3 := fun c => by compute_degree
  have hd := hdeg (hairerWickConstant N ρ ε)
  have hd' := hdeg (hairerWickConstant N ρ' ε')
  have h := hA hW (continuous_hairerPsiField N hξ.1) (continuous_hairerPsiField N hξ'.1)
    (measurable_hairerPsiField_apply N hξ) (measurable_hairerPsiField_apply N hξ')
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (exists_hairerPsiField_pairing N hρ' hε' hW hξ')
    (V := max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0))
    (fun z => (integral_hairerPsiField_sq_le N hρ hε hW hξ z).trans (le_max_left _ _))
    (fun z => (integral_hairerPsiField_sq_le N hρ' hε' hW hξ' z).trans (le_max_right _ _))
    hgm hgi (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X) (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ' ε') * Polynomial.X) hd hd'
  have e : ∀ ω, ∫ w, (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w) * semigroupPeriodised t z w =
      ∫ y, ((Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X).eval (hairerPsiField N ξ ω y) - (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ' ε') * Polynomial.X).eval (hairerPsiField N ξ' ω y)) *
        semigroupPeriodised t z y := fun ω => by
    simp [hairerPsiWickCube]
  simp only [e]
  exact h

end RegularityStructures.Phi43

end
