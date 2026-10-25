/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiPsiSqXPeriodise
public import Phi43.BPHZ.SemigroupTestDiffMoments
public import Phi43.BPHZ.SemigroupTestAllMomentsSetup
public import Phi43.BPHZ.SemigroupTestAllMoments
public import Phi43.BPHZ.TreeWickSquare

/-!
# All moments of the Wick square tested against the coordinate-weighted kernel

For a test function `g_i = semigroupPeriodisedX t z i` and `p ≥ 1`, the tested Wick square
`X = ∫ :Ψ²:_ε g_i` (and the tested cross-mollifier difference) has integrable `2p`-th power and
`E X^(2p) ≤ A (E X²)^p` with `A = A(p)` independent of everything else.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem semigroupPeriodisedX_chaos_data {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) (i : Fin 3) :
    Measurable (semigroupPeriodisedX t z i) ∧ Integrable (semigroupPeriodisedX t z i) := by
  have hm := measurable_semigroupPeriodisedX t z i
  refine ⟨hm, ?_⟩
  have h := (integral_abs_semigroupPeriodisedX_mul_le ht (le_refl (0 : ℝ)) z i).1
  simp only [Real.rpow_zero, mul_one] at h
  exact (integrable_norm_iff hm.aestronglyMeasurable).1 (by simpa using h)

/-- **All moments of the tested Wick square against `g_i`, with integrability.** -/
theorem hairerPsiWickSquare_semigroupPeriodisedX_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ (z : ParabolicSpace) (i : Fin 3),
        Integrable (fun ω => (∫ w, hairerPsiWickSquare N ρ ε ξ ω w *
          semigroupPeriodisedX t z i w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, hairerPsiWickSquare N ρ ε ξ ω w * semigroupPeriodisedX t z i w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, hairerPsiWickSquare N ρ ε ξ ω w *
            semigroupPeriodisedX t z i w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u} 2 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ {t} ht z i => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodisedX_chaos_data ht z i
  set Q : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε) with hQ
  have hdeg : Q.natDegree ≤ 2 := by rw [hQ]; compute_degree
  have h := hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    hgm hgi Q hdeg
  have e : ∀ ω, ∫ w, hairerPsiWickSquare N ρ ε ξ ω w * semigroupPeriodisedX t z i w =
      ∫ y, Q.eval (hairerPsiField N ξ ω y) * semigroupPeriodisedX t z i y := fun ω => by
    simp [hQ, hairerPsiWickSquare]
  simp only [e]
  exact h

/-- **All moments of the tested cross-mollifier difference of `:Ψ²:` against `g_i`.** -/
theorem hairerPsiWickSquare_sub_semigroupPeriodisedX_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → ∀ (z : ParabolicSpace) (i : Fin 3),
        Integrable (fun ω => (∫ w, (hairerPsiWickSquare N ρ ε ξ ω w -
          hairerPsiWickSquare N ρ' ε' ξ' ω w) * semigroupPeriodisedX t z i w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w) *
            semigroupPeriodisedX t z i w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, (hairerPsiWickSquare N ρ ε ξ ω w -
            hairerPsiWickSquare N ρ' ε' ξ' ω w) * semigroupPeriodisedX t z i w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub_timeTruncation.{u} 2 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' {t} ht z i => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodisedX_chaos_data ht z i
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
    hgm hgi (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε))
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ' ε')) hd hd'
  have e : ∀ ω, ∫ w, (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w) *
      semigroupPeriodisedX t z i w =
      ∫ y, ((Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε)).eval
        (hairerPsiField N ξ ω y) - (Polynomial.X ^ 2 -
          Polynomial.C (hairerWickConstant N ρ' ε')).eval (hairerPsiField N ξ' ω y)) *
        semigroupPeriodisedX t z i y := fun ω => by
    simp [hairerPsiWickSquare]
  simp only [e]
  exact h

end RegularityStructures.Phi43

end
