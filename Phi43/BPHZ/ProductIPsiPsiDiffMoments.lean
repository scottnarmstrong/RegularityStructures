/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiMoments
public import Phi43.BPHZ.ProductIPsiPsiDiffMomentsIntegrable
public import RegularityStructures.BPHZ.ChaosLimitMomentsTwoFieldsKernelTruncation

/-!
# All moments of the tested two-mollifier differences of `I(Ψ)Ψ` and `I(Ψ)(Ψ² - c₁)`

For two regularised noises of the same white noise and the semigroup test `Q_t(x, ·)` on `ℝ⁴`,
`E |X - X'|^(2p) ≤ A (E |X - X'|²)^p` with `A = A(p)`, where `X`, `X'` are the tested fields of
`hairerIPsiPsiField` (resp. `hairerIPsiPsiSqField`).  After the lattice reduction to `ℝ × T³`
both tested fields are `∫ chaosField · g`, and
`integrable_and_integral_pow_two_mul_le_of_chaosField_sub_timeTruncation` applies.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **All moments of the tested two-mollifier difference of the field of `I(Ψ)Ψ`.** -/
theorem hairerIPsiPsiField_semigroup_sub_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → ∀ x : ParabolicSpace,
        Integrable (fun ω => ((∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) -
            ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ' x ω y) ^ (2 * p)) P ∧
        ∫ ω, ((∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) -
            ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ' x ω y) ^ (2 * p) ∂P ≤
          A * (∫ ω, ((∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) -
            ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ' x ω y) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_chaosField_sub_timeTruncation.{u} 3 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' {t} ht x => ?_⟩
  obtain ⟨L, hL0, hL⟩ := integral_abs_hairerTaylorKernel_le N
  have key := hA hW (continuous_hairerPsiField N hξ.1) (continuous_hairerPsiField N hξ'.1)
    (measurable_hairerPsiField_apply N hξ) (measurable_hairerPsiField_apply N hξ')
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (exists_hairerPsiField_pairing N hρ' hε' hW hξ')
    (V := max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0))
    (fun z => (integral_hairerPsiField_sq_le N hρ hε hW hξ z).trans (le_max_left _ _))
    (fun z => (integral_hairerPsiField_sq_le N hρ' hε' hW hξ' z).trans (le_max_right _ _))
    (measurable_latticeG t x) (integrable_latticeG ht x) (measurable_uncurry_latticeK N t x)
    (fun u => (integrable_latticeK_and_integral_abs_le hL0 hL t x u).1)
    (fun u => (integrable_latticeK_and_integral_abs_le hL0 hL t x u).2)
    (fun c R => latticeK_support N t x c R) Polynomial.X Polynomial.X 0
    Polynomial.X Polynomial.X 0
    (by rw [Polynomial.natDegree_X]; omega) (by simp)
    (by rw [Polynomial.natDegree_X]; omega) (by simp)
  have hae : ∀ᵐ ω ∂P, (∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) -
        ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ' x ω y =
      ∫ v, (chaosField (hairerPsiField N ξ) (latticeK N t x) Polynomial.X Polynomial.X 0 ω v -
        chaosField (hairerPsiField N ξ') (latticeK N t x) Polynomial.X Polynomial.X 0 ω v) *
          latticeG t x v := by
    filter_upwards [ae_integrable_semigroup_hairerIPsiPsiField N hρ hW hε hξ ht x,
      ae_integrable_semigroup_hairerIPsiPsiField N hρ' hW hε' hξ' ht x] with ω hi hi'
    have h := integral_semigroup_mul_iPsi_field_eq hL0 hL (hξ.1 ω)
      (Φ := hairerPsiField N ξ ω) (continuous_hairerPsiField N hξ.1 ω).measurable ht x hi
    have h' := integral_semigroup_mul_iPsi_field_eq hL0 hL (hξ'.1 ω)
      (Φ := hairerPsiField N ξ' ω) (continuous_hairerPsiField N hξ'.1 ω).measurable ht x hi'
    have j := integrable_latticeIntegrand_of_integrable_semigroup_mul_iPsi_field hL0 hL (hξ.1 ω)
      (Φ := hairerPsiField N ξ ω) (continuous_hairerPsiField N hξ.1 ω).measurable ht x hi
    have j' := integrable_latticeIntegrand_of_integrable_semigroup_mul_iPsi_field hL0 hL (hξ'.1 ω)
      (Φ := hairerPsiField N ξ' ω) (continuous_hairerPsiField N hξ'.1 ω).measurable ht x hi'
    simp only [hairerIPsiPsiField]
    rw [h, h']
    simp only [chaosField, Polynomial.eval_X, Polynomial.eval_zero, sub_mul]
    rw [integral_sub j j']
  refine ⟨?_, ?_⟩
  · refine key.1.congr ?_
    filter_upwards [hae] with ω h
    rw [h]
  · have e1 : ∫ ω, ((∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) -
        ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ' x ω y) ^ (2 * p) ∂P =
        ∫ ω, (∫ v, (chaosField (hairerPsiField N ξ) (latticeK N t x) Polynomial.X Polynomial.X 0 ω v -
        chaosField (hairerPsiField N ξ') (latticeK N t x) Polynomial.X Polynomial.X 0 ω v) *
          latticeG t x v) ^ (2 * p) ∂P :=
      integral_congr_ae (hae.mono fun ω h => by beta_reduce; rw [h])
    have e2 : ∫ ω, ((∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) -
        ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ' x ω y) ^ 2 ∂P =
        ∫ ω, (∫ v, (chaosField (hairerPsiField N ξ) (latticeK N t x) Polynomial.X Polynomial.X 0 ω v -
        chaosField (hairerPsiField N ξ') (latticeK N t x) Polynomial.X Polynomial.X 0 ω v) *
          latticeG t x v) ^ 2 ∂P :=
      integral_congr_ae (hae.mono fun ω h => by beta_reduce; rw [h])
    rw [e1, e2]
    exact key.2

end RegularityStructures.Phi43

end
