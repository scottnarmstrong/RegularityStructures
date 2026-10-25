/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestDiffMoments
public import Phi43.BPHZ.SemigroupTestAllMomentsSetup
public import Phi43.BPHZ.SemigroupTestAllMoments

/-!
# All moments of the tested difference of two regularised noises, with integrability

For regularised noises `ξ`, `ξ'` of the same white noise and `p ≥ 1`, the tested difference
`X = ∫ (ξ - ξ') q^♯_t(z, ·)` has integrable `2p`-th power and `E X^(2p) ≤ A (E X²)^p` with
`A = A(p)` independent of everything else
(`regularisedNoise_sub_semigroupPeriodised_integrable_pow_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **All moments of the tested difference of two regularised noises, semigroup test.** -/
theorem regularisedNoise_sub_semigroupPeriodised_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ}, IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → ∀ z : ParabolicSpace,
        Integrable (fun ω => (∫ w, (ξ ω w - ξ' ω w) * semigroupPeriodised t z w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, (ξ ω w - ξ' ω w) * semigroupPeriodised t z w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, (ξ ω w - ξ' ω w) * semigroupPeriodised t z w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub_timeTruncation.{u} 1 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} hρ hρ' hW hε hε' hξ hξ' {t} ht z => ?_⟩
  obtain ⟨hgm, hgi⟩ := semigroupPeriodised_chaos_data ht z
  have hd : (Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by simp
  have h := hA hW (fun ω => IsSmoothOnSpaceTime.continuous (hξ.1 ω))
    (fun ω => IsSmoothOnSpaceTime.continuous (hξ'.1 ω))
    (fun y => (hξ.2 y).1) (fun y => (hξ'.2 y).1)
    (exists_regularisedNoise_pairing hρ hε hξ) (exists_regularisedNoise_pairing hρ' hε' hξ')
    (V := max (∫ w, periodise ρ ε w ^ 2) (∫ w, periodise ρ' ε' w ^ 2))
    (fun y => (integral_regularisedNoise_sq_le hρ hε hW hξ y).trans (le_max_left _ _))
    (fun y => (integral_regularisedNoise_sq_le hρ' hε' hW hξ' y).trans (le_max_right _ _))
    hgm hgi Polynomial.X Polynomial.X hd hd
  have e : ∀ ω, ∫ w, (ξ ω w - ξ' ω w) * semigroupPeriodised t z w =
      ∫ y, (Polynomial.X.eval (ξ ω y) - Polynomial.X.eval (ξ' ω y)) *
        semigroupPeriodised t z y := fun ω => by
    simp
  simp only [e]
  exact h

end RegularityStructures.Phi43

end
