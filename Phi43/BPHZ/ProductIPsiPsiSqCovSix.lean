/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiCovFour
public import Phi43.BPHZ.TreeWickSquareFour
import Mathlib.Tactic
public import Phi43.BPHZ.TreeWickSquare

/-!
# Six-point formula for `Ψ` and the Wick-square block `E[Ψ(w) :Ψ(a)²: Ψ(w') :Ψ(b)²:]`

* `hairerPsiField_integral_mul_six`: Gaussian integration by parts on the first factor reduces the
  six-point expectation to five four-point expectations;
* `hairerPsiField_wick_block`: with `Q = hairerCovariance`, `c = Q(0)`,
  `E[Ψ(w) (Ψ(a)² - c) Ψ(w') (Ψ(b)² - c)] =
    2 Q(w - w') Q(a - b)² + 4 Q(w - a) Q(w' - b) Q(a - b) + 4 Q(w - b) Q(a - w') Q(a - b)`;
* the uniform `L¹` bound `E |Ψ(w) (Ψ(a)² - c) Ψ(w') (Ψ(b)² - c)| ≤ 3 c² + 60 c⁴`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- The four-point expression of `hairerPsiField_integral_mul_four`. -/
def psiFourPoint (Q : SpaceTime → ℝ) (a b c d : SpaceTime) : ℝ :=
  Q (a - b) * Q (c - d) + Q (a - c) * Q (b - d) + Q (a - d) * Q (b - c)

/-- **Six-point formula for `Ψ`.** -/
theorem hairerPsiField_integral_mul_six (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (p₀ p₁ p₂ p₃ p₄ p₅ : SpaceTime) :
    ∫ ω, hairerPsiField N ξ ω p₀ * hairerPsiField N ξ ω p₁ * hairerPsiField N ξ ω p₂ *
        hairerPsiField N ξ ω p₃ * hairerPsiField N ξ ω p₄ * hairerPsiField N ξ ω p₅ ∂P =
      hairerCovariance N ρ ε (p₀ - p₁) * psiFourPoint (hairerCovariance N ρ ε) p₂ p₃ p₄ p₅ +
      hairerCovariance N ρ ε (p₀ - p₂) * psiFourPoint (hairerCovariance N ρ ε) p₁ p₃ p₄ p₅ +
      hairerCovariance N ρ ε (p₀ - p₃) * psiFourPoint (hairerCovariance N ρ ε) p₁ p₂ p₄ p₅ +
      hairerCovariance N ρ ε (p₀ - p₄) * psiFourPoint (hairerCovariance N ρ ε) p₁ p₂ p₃ p₅ +
      hairerCovariance N ρ ε (p₀ - p₅) * psiFourPoint (hairerCovariance N ρ ε) p₁ p₂ p₃ p₄ := by
  have h := hairerPsiField_isCentredGaussianVector N hρ hε hW hξ ![p₀, p₁, p₂, p₃, p₄, p₅]
  have hP := h.isProbabilityMeasure
  have e : ∀ ω, hairerPsiField N ξ ω p₀ * hairerPsiField N ξ ω p₁ * hairerPsiField N ξ ω p₂ *
        hairerPsiField N ξ ω p₃ * hairerPsiField N ξ ω p₄ * hairerPsiField N ξ ω p₅ =
        (fun ω (i : Fin 6) => hairerPsiField N ξ ω (![p₀, p₁, p₂, p₃, p₄, p₅] i)) ω 0 *
          ∏ k ∈ ({1, 2, 3, 4, 5} : Finset (Fin 6)),
            (fun ω (i : Fin 6) => hairerPsiField N ξ ω (![p₀, p₁, p₂, p₃, p₄, p₅] i)) ω k := by
    intro ω
    simp [Finset.prod_insert, mul_assoc]
  simp_rw [e]
  rw [h.integral_mul_prod_eq_sum (σ := fun i : Fin 6 => i) 0 ({1, 2, 3, 4, 5} : Finset (Fin 6))]
  have e1 : ({1, 2, 3, 4, 5} : Finset (Fin 6)).erase 1 = {2, 3, 4, 5} := by decide
  have e2 : ({1, 2, 3, 4, 5} : Finset (Fin 6)).erase 2 = {1, 3, 4, 5} := by decide
  have e3 : ({1, 2, 3, 4, 5} : Finset (Fin 6)).erase 3 = {1, 2, 4, 5} := by decide
  have e4 : ({1, 2, 3, 4, 5} : Finset (Fin 6)).erase 4 = {1, 2, 3, 5} := by decide
  have e5 : ({1, 2, 3, 4, 5} : Finset (Fin 6)).erase 5 = {1, 2, 3, 4} := by decide
  have hsum : ∀ f : Fin 6 → ℝ, ∑ j ∈ ({1, 2, 3, 4, 5} : Finset (Fin 6)), f j =
      f 1 + f 2 + f 3 + f 4 + f 5 := by
    intro f
    simp [Finset.sum_insert, add_assoc]
  rw [hsum]
  simp only [e1, e2, e3, e4, e5]
  have f4 := fun a b c d => (hairerPsiField_integral_mul_four N hρ hε hW hξ a b c d).2
  have P4 : ∀ (i j k l : Fin 6), i ∉ ({j, k, l} : Finset (Fin 6)) → j ∉ ({k, l} : Finset (Fin 6)) →
      k ≠ l → ∫ ω, ∏ x ∈ ({i, j, k, l} : Finset (Fin 6)),
        hairerPsiField N ξ ω (![p₀, p₁, p₂, p₃, p₄, p₅] x) ∂P =
        psiFourPoint (hairerCovariance N ρ ε) (![p₀, p₁, p₂, p₃, p₄, p₅] i)
          (![p₀, p₁, p₂, p₃, p₄, p₅] j) (![p₀, p₁, p₂, p₃, p₄, p₅] k)
          (![p₀, p₁, p₂, p₃, p₄, p₅] l) := by
    intro i j k l hi hj hk
    simp only [Finset.prod_insert hi, Finset.prod_insert hj, Finset.prod_pair hk]
    have := f4 (![p₀, p₁, p₂, p₃, p₄, p₅] i) (![p₀, p₁, p₂, p₃, p₄, p₅] j)
      (![p₀, p₁, p₂, p₃, p₄, p₅] k) (![p₀, p₁, p₂, p₃, p₄, p₅] l)
    simp_rw [← mul_assoc]
    rw [this]
    rfl
  rw [P4 2 3 4 5 (by decide) (by decide) (by decide), P4 1 3 4 5 (by decide) (by decide) (by decide),
    P4 1 2 4 5 (by decide) (by decide) (by decide), P4 1 2 3 5 (by decide) (by decide) (by decide),
    P4 1 2 3 4 (by decide) (by decide) (by decide)]
  rfl

/-- Integrability of the six-fold product. -/
theorem integrable_hairerPsiField_mul_six (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (p₀ p₁ p₂ p₃ p₄ p₅ : SpaceTime) :
    Integrable (fun ω => hairerPsiField N ξ ω p₀ * hairerPsiField N ξ ω p₁ *
      hairerPsiField N ξ ω p₂ * hairerPsiField N ξ ω p₃ * hairerPsiField N ξ ω p₄ *
      hairerPsiField N ξ ω p₅) P := by
  have h := hairerPsiField_isCentredGaussianVector N hρ hε hW hξ ![p₀, p₁, p₂, p₃, p₄, p₅]
  have := h.integrable_prod_apply (σ := fun i : Fin 6 => i) Finset.univ
  simpa [Fin.prod_univ_six, mul_assoc] using this

/-- **The Wick-square block.** -/
theorem hairerPsiField_wick_block (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (w a w' b : SpaceTime) :
    ∫ ω, hairerPsiField N ξ ω w * (hairerPsiField N ξ ω a ^ 2 - hairerCovariance N ρ ε 0) *
        hairerPsiField N ξ ω w' * (hairerPsiField N ξ ω b ^ 2 - hairerCovariance N ρ ε 0) ∂P =
      2 * hairerCovariance N ρ ε (w - w') * hairerCovariance N ρ ε (a - b) ^ 2 +
      4 * (hairerCovariance N ρ ε (w - a) * hairerCovariance N ρ ε (w' - b) *
        hairerCovariance N ρ ε (a - b)) +
      4 * (hairerCovariance N ρ ε (w - b) * hairerCovariance N ρ ε (a - w') *
        hairerCovariance N ρ ε (a - b)) := by
  set Q := hairerCovariance N ρ ε with hQ
  set Y := fun (z : SpaceTime) (ω : Ω) => hairerPsiField N ξ ω z with hY
  have i6 := integrable_hairerPsiField_mul_six N hρ hε hW hξ w a a w' b b
  have i4a := (hairerPsiField_integral_mul_four N hρ hε hW hξ w w' b b).1
  have i4b := (hairerPsiField_integral_mul_four N hρ hε hW hξ w a a w').1
  have i2 : Integrable (fun ω => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w') P :=
    (hairerPsiField_integral_abs_mul_two_le N hρ hε hW hξ w w').1
  have s6 := hairerPsiField_integral_mul_six N hρ hε hW hξ w a a w' b b
  have s4a := (hairerPsiField_integral_mul_four N hρ hε hW hξ w w' b b).2
  have s4b := (hairerPsiField_integral_mul_four N hρ hε hW hξ w a a w').2
  have s2 := hairerPsiField_integral_mul N hρ hε hW hξ w w'
  have e : ∀ ω, hairerPsiField N ξ ω w * (hairerPsiField N ξ ω a ^ 2 - Q 0) *
        hairerPsiField N ξ ω w' * (hairerPsiField N ξ ω b ^ 2 - Q 0) =
      ((hairerPsiField N ξ ω w * hairerPsiField N ξ ω a * hairerPsiField N ξ ω a *
        hairerPsiField N ξ ω w' * hairerPsiField N ξ ω b * hairerPsiField N ξ ω b) -
        Q 0 * (hairerPsiField N ξ ω w * hairerPsiField N ξ ω w' * hairerPsiField N ξ ω b *
          hairerPsiField N ξ ω b)) -
        Q 0 * (hairerPsiField N ξ ω w * hairerPsiField N ξ ω a * hairerPsiField N ξ ω a *
          hairerPsiField N ξ ω w') +
        Q 0 ^ 2 * (hairerPsiField N ξ ω w * hairerPsiField N ξ ω w') := fun ω => by ring
  simp_rw [e]
  have j1 : Integrable (fun ω => (hairerPsiField N ξ ω w * hairerPsiField N ξ ω a *
      hairerPsiField N ξ ω a * hairerPsiField N ξ ω w' * hairerPsiField N ξ ω b *
        hairerPsiField N ξ ω b) -
      Q 0 * (hairerPsiField N ξ ω w * hairerPsiField N ξ ω w' * hairerPsiField N ξ ω b *
        hairerPsiField N ξ ω b)) P := i6.sub (i4a.const_mul _)
  have j2 : Integrable (fun ω => ((hairerPsiField N ξ ω w * hairerPsiField N ξ ω a *
      hairerPsiField N ξ ω a * hairerPsiField N ξ ω w' * hairerPsiField N ξ ω b *
        hairerPsiField N ξ ω b) -
      Q 0 * (hairerPsiField N ξ ω w * hairerPsiField N ξ ω w' * hairerPsiField N ξ ω b *
        hairerPsiField N ξ ω b)) -
      Q 0 * (hairerPsiField N ξ ω w * hairerPsiField N ξ ω a * hairerPsiField N ξ ω a *
        hairerPsiField N ξ ω w')) P := j1.sub (i4b.const_mul _)
  rw [integral_add j2 (i2.const_mul _), integral_sub j1 (i4b.const_mul _),
    integral_sub i6 (i4a.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul,
    s6, s4a, s4b, s2]
  simp only [psiFourPoint, sub_self]
  ring

/-- **Uniform `L¹` bound of the Wick-square block**, `c = Q(0)`. -/
theorem hairerPsiField_wick_block_abs_le (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (w a w' b : SpaceTime) :
    Integrable (fun ω => hairerPsiField N ξ ω w *
      (hairerPsiField N ξ ω a ^ 2 - hairerCovariance N ρ ε 0) * hairerPsiField N ξ ω w' *
        (hairerPsiField N ξ ω b ^ 2 - hairerCovariance N ρ ε 0)) P ∧
    ∫ ω, |hairerPsiField N ξ ω w * (hairerPsiField N ξ ω a ^ 2 - hairerCovariance N ρ ε 0) *
      hairerPsiField N ξ ω w' * (hairerPsiField N ξ ω b ^ 2 - hairerCovariance N ρ ε 0)| ∂P ≤
      (3 * hairerCovariance N ρ ε 0 ^ 2 + 60 * hairerCovariance N ρ ε 0 ^ 4 +
        3 * hairerCovariance N ρ ε 0 ^ 2 + 60 * hairerCovariance N ρ ε 0 ^ 4) / 4 := by
  have hwc : hairerWickConstant N ρ ε = hairerCovariance N ρ ε 0 :=
    hairerWickConstant_eq_covariance_zero N ρ ε
  have hS : ∀ z ω, hairerPsiField N ξ ω z ^ 2 - hairerCovariance N ρ ε 0 =
      hairerPsiWickSquare N ρ ε ξ ω z := fun z ω => by
    rw [hairerPsiWickSquare, hwc]
  have hS4i : ∀ z, Integrable (fun ω => (hairerPsiField N ξ ω z ^ 2 -
      hairerCovariance N ρ ε 0) ^ 4) P := fun z => by
    simp only [hS]
    exact integrable_hairerPsiWickSquare_pow_four N hρ hε hW hξ z
  have hS4 : ∀ z, ∫ ω, (hairerPsiField N ξ ω z ^ 2 - hairerCovariance N ρ ε 0) ^ 4 ∂P =
      60 * hairerCovariance N ρ ε 0 ^ 4 := fun z => by
    simp only [hS]
    rw [integral_hairerPsiWickSquare_pow_four N hρ hε hW hξ z, hwc]
  have hΨ4 : ∀ z : SpaceTime, Integrable (fun ω => hairerPsiField N ξ ω z ^ 4) P := fun z => by
    have := (hairerPsiField_integral_mul_four N hρ hε hW hξ z z z z).1
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only; ring
  have mΨ : ∀ z, Measurable (fun ω => hairerPsiField N ξ ω z) := fun z =>
    measurable_hairerPsiField_apply N hξ z
  have mS : ∀ z, Measurable (fun ω => hairerPsiField N ξ ω z ^ 2 - hairerCovariance N ρ ε 0) :=
    fun z => ((mΨ z).pow_const 2).sub_const _
  have hm : Measurable (fun ω => hairerPsiField N ξ ω w * (hairerPsiField N ξ ω a ^ 2 -
      hairerCovariance N ρ ε 0) * hairerPsiField N ξ ω w' * (hairerPsiField N ξ ω b ^ 2 -
      hairerCovariance N ρ ε 0)) := (((mΨ w).mul (mS a)).mul (mΨ w')).mul (mS b)
  have s12 : Integrable (fun ω => hairerPsiField N ξ ω w ^ 4 +
      (hairerPsiField N ξ ω a ^ 2 - hairerCovariance N ρ ε 0) ^ 4) P := (hΨ4 w).add (hS4i a)
  have s123 : Integrable (fun ω => hairerPsiField N ξ ω w ^ 4 +
      (hairerPsiField N ξ ω a ^ 2 - hairerCovariance N ρ ε 0) ^ 4 +
      hairerPsiField N ξ ω w' ^ 4) P := s12.add (hΨ4 w')
  have s1234 : Integrable (fun ω => hairerPsiField N ξ ω w ^ 4 +
      (hairerPsiField N ξ ω a ^ 2 - hairerCovariance N ρ ε 0) ^ 4 +
      hairerPsiField N ξ ω w' ^ 4 +
      (hairerPsiField N ξ ω b ^ 2 - hairerCovariance N ρ ε 0) ^ 4) P := s123.add (hS4i b)
  have hdom : Integrable (fun ω => (hairerPsiField N ξ ω w ^ 4 +
      (hairerPsiField N ξ ω a ^ 2 - hairerCovariance N ρ ε 0) ^ 4 +
      hairerPsiField N ξ ω w' ^ 4 +
      (hairerPsiField N ξ ω b ^ 2 - hairerCovariance N ρ ε 0) ^ 4) / 4) P := s1234.div_const 4
  have hpt : ∀ ω, |hairerPsiField N ξ ω w * (hairerPsiField N ξ ω a ^ 2 -
      hairerCovariance N ρ ε 0) * hairerPsiField N ξ ω w' * (hairerPsiField N ξ ω b ^ 2 -
      hairerCovariance N ρ ε 0)| ≤ (hairerPsiField N ξ ω w ^ 4 +
      (hairerPsiField N ξ ω a ^ 2 - hairerCovariance N ρ ε 0) ^ 4 +
      hairerPsiField N ξ ω w' ^ 4 +
      (hairerPsiField N ξ ω b ^ 2 - hairerCovariance N ρ ε 0) ^ 4) / 4 := fun ω =>
    abs_mul_four_le_pow_four _ _ _ _
  have hi : Integrable (fun ω => hairerPsiField N ξ ω w * (hairerPsiField N ξ ω a ^ 2 -
      hairerCovariance N ρ ε 0) * hairerPsiField N ξ ω w' * (hairerPsiField N ξ ω b ^ 2 -
      hairerCovariance N ρ ε 0)) P :=
    hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hpt ω)
  refine ⟨hi, (integral_mono hi.abs hdom hpt).trans (le_of_eq ?_)⟩
  rw [integral_div, integral_add s123 (hS4i b), integral_add s12 (hΨ4 w'),
    integral_add (hΨ4 w) (hS4i a), hS4, hS4,
    hairerPsiField_integral_pow_four N hρ hε hW hξ, hairerPsiField_integral_pow_four N hρ hε hW hξ]

end RegularityStructures.Phi43

end
