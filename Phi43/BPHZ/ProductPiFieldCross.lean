/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiFieldMoment
public import Phi43.BPHZ.CrossMollifierGaussian

/-!
# The covariance of `I₂Ψ` at two mollifiers and two scales

The fields `I₂Ψ_{ρ,ε}` and `I₂Ψ_{ρ',ε'}` built from different mollifiers of the same white noise:
the four-point Gaussian vector is that of
`hairerPsiField_isCentredGaussianVector_multiscaleTwo`, and the block formula of
`isqBlockKernel` holds with `Q_{εε'} = hairerCrossCovarianceTwo N ρ ε ρ' ε'`.
Cross-mollifier version of `ProductPiField`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- The four-point Gaussian vector `(Ψ_{ρ,ε}(w), Ψ_{ρ,ε}(y), Ψ_{ρ',ε'}(w̄), Ψ_{ρ',ε'}(ȳ))`. -/
private theorem hairerPsiField_isCentredGaussianVector_four_cross (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hε : 0 < ε) (hε' : 0 < ε') (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (w y w' y' : SpaceTime) :
    IsCentredGaussianVector P
      (fun ω (i : Fin 4) => hairerPsiField N (![ξ, ξ, ξ', ξ'] i) ω (![w, y, w', y'] i))
      (fun i j => hairerCrossCovarianceTwo N (![ρ, ρ, ρ', ρ'] i) (![ε, ε, ε', ε'] i)
        (![ρ, ρ, ρ', ρ'] j) (![ε, ε, ε', ε'] j) (![w, y, w', y'] i - ![w, y, w', y'] j)) :=
  hairerPsiField_isCentredGaussianVector_multiscaleTwo N (ρ := ![ρ, ρ, ρ', ρ'])
    (ε := ![ε, ε, ε', ε']) (ξ := ![ξ, ξ, ξ', ξ']) (fun i => by fin_cases i <;> simpa)
    (fun i => by fin_cases i <;> simpa) hW (fun i => by fin_cases i <;> simpa) ![w, y, w', y']

/-- **Pointwise moment data for `:Ψ_{ρ,ε}²:(w) Ψ_{ρ,ε}(y) :Ψ_{ρ',ε'}²:(w̄) Ψ_{ρ',ε'}(ȳ)`**:
integrability, the uniform bound `E|·| ≤ 42 (max c_{ρ,ε} c_{ρ',ε'})⁴`, and the Wick-block formula
for the expectation. -/
theorem hairerPsiWickSquare_pair_data_cross (N : ℕ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    (hε : 0 < ε) (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (w y w' y' : SpaceTime) :
    Integrable (fun ω => hairerPsiWickSquare N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickSquare N ρ' ε' ξ' ω w' * hairerPsiField N ξ' ω y')) P ∧
    ∫ ω, |hairerPsiWickSquare N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickSquare N ρ' ε' ξ' ω w' * hairerPsiField N ξ' ω y')| ∂P ≤
      10 * (max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ' ε')) ^ 3 ∧
    ∫ ω, hairerPsiWickSquare N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickSquare N ρ' ε' ξ' ω w' * hairerPsiField N ξ' ω y') ∂P =
      isqBlockKernel (hairerCovariance N ρ ε) (hairerCrossCovarianceTwo N ρ ε ρ' ε')
        (hairerCovariance N ρ' ε') (hairerCrossCovarianceTwo N ρ ε ρ' ε')
        (hairerCrossCovarianceTwo N ρ ε ρ' ε') (hairerCrossCovarianceTwo N ρ ε ρ' ε')
        w y w' y' := by
  have h := hairerPsiField_isCentredGaussianVector_four_cross N hρ hρ' hε hε' hW hξ hξ' w y w' y'
  have hD : ∀ i, hairerCrossCovarianceTwo N (![ρ, ρ, ρ', ρ'] i) (![ε, ε, ε', ε'] i)
      (![ρ, ρ, ρ', ρ'] i) (![ε, ε, ε', ε'] i) (![w, y, w', y'] i - ![w, y, w', y'] i) ≤
      max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ' ε') := by
    intro i
    fin_cases i <;> simp [hairerCrossCovarianceTwo_self, hairerCrossCovariance_self,
      ← hairerWickConstant_eq_covariance_zero]
  have hmom := h.integrable_and_abs_integral_wick_two_le hD 0 1 2 3
  have hform := integral_wick_two_mul_X_mul_wick_two_mul_X h 0 1 2 3
  have e : ∀ ω, hairerPsiWickSquare N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickSquare N ρ' ε' ξ' ω w' * hairerPsiField N ξ' ω y') =
      wickMonomial (fun i j => hairerCrossCovarianceTwo N (![ρ, ρ, ρ', ρ'] i) (![ε, ε, ε', ε'] i)
        (![ρ, ρ, ρ', ρ'] j) (![ε, ε, ε', ε'] j) (![w, y, w', y'] i - ![w, y, w', y'] j))
        (List.replicate 2 0) (fun i => hairerPsiField N (![ξ, ξ, ξ', ξ'] i) ω (![w, y, w', y'] i))
        * hairerPsiField N (![ξ, ξ, ξ', ξ'] 1) ω (![w, y, w', y'] 1) *
        wickMonomial (fun i j => hairerCrossCovarianceTwo N (![ρ, ρ, ρ', ρ'] i) (![ε, ε, ε', ε'] i)
        (![ρ, ρ, ρ', ρ'] j) (![ε, ε, ε', ε'] j) (![w, y, w', y'] i - ![w, y, w', y'] j))
        (List.replicate 2 2) (fun i => hairerPsiField N (![ξ, ξ, ξ', ξ'] i) ω (![w, y, w', y'] i))
        * hairerPsiField N (![ξ, ξ, ξ', ξ'] 3) ω (![w, y, w', y'] 3) := by
    intro ω
    rw [show List.replicate 2 (0 : Fin 4) = [0, 0] from rfl,
      show List.replicate 2 (2 : Fin 4) = [2, 2] from rfl, wickMonomial_pair_self,
      wickMonomial_pair_self]
    simp [hairerPsiWickSquare, hairerCrossCovarianceTwo_self, hairerCrossCovariance_self,
      ← hairerWickConstant_eq_covariance_zero]
    ring
  simp only [e]
  refine ⟨hmom.1, hmom.2, ?_⟩
  rw [hform]
  simp [isqBlockKernel, hairerCrossCovarianceTwo_self, hairerCrossCovariance_self]

/-- **Covariance identity, general kernels, two mollifiers.** For integrable `g, g'`,
`E[((∫ g :Ψ_{ρ,ε}²:) Ψ_{ρ,ε}(y)) ((∫ g' :Ψ_{ρ',ε'}²:) Ψ_{ρ',ε'}(ȳ))] =
  ∫∫ g(w) g'(w̄) isqBlockKernel Q_{ρε} Q_{ρε,ρ'ε'} Q_{ρ'ε'} Q_{ρε,ρ'ε'} Q_{ρε,ρ'ε'}
    Q_{ρε,ρ'ε'} w y w̄ ȳ dw dw̄`. -/
theorem hairerPsiWickSquare_testedPair_integral_cross (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hε : 0 < ε) (hε' : 0 < ε') (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    {g g' : SpaceTime → ℝ} (hg : Integrable g) (hg' : Integrable g') (y y' : SpaceTime) :
    ∫ ω, ((∫ w, g w * hairerPsiWickSquare N ρ ε ξ ω w) * hairerPsiField N ξ ω y) *
        ((∫ w, g' w * hairerPsiWickSquare N ρ' ε' ξ' ω w) * hairerPsiField N ξ' ω y') ∂P =
      ∫ w, ∫ w', g w * g' w' * isqBlockKernel (hairerCovariance N ρ ε)
        (hairerCrossCovarianceTwo N ρ ε ρ' ε') (hairerCovariance N ρ' ε')
        (hairerCrossCovarianceTwo N ρ ε ρ' ε') (hairerCrossCovarianceTwo N ρ ε ρ' ε')
        (hairerCrossCovarianceTwo N ρ ε ρ' ε') w y w' y' := by
  have := hW.isProbabilityMeasure
  have hdata := fun q : SpaceTime × SpaceTime =>
    hairerPsiWickSquare_pair_data_cross N hρ hρ' hε hε' hW hξ hξ' q.1 y q.2 y'
  have hY := measurable_hairerPsiWickSquare_uncurry N hξ
  have hY' := measurable_hairerPsiWickSquare_uncurry N hξ'
  have ha := measurable_hairerPsiField_apply N hξ y
  have hb := measurable_hairerPsiField_apply N hξ' y'
  have hi := fun q : SpaceTime × SpaceTime => (hdata q).1
  have hM := fun q : SpaceTime × SpaceTime => (hdata q).2.1
  have hfub := integral_testedPair_eq hY hY' ha hb hg hg' hi hM
  have hexp := integrable_testedPair_expectation hY hY' ha hb hg hg' hi hM
  have hpt : ∀ q : SpaceTime × SpaceTime, g q.1 * g' q.2 *
      ∫ ω, hairerPsiWickSquare N ρ ε ξ ω q.1 * hairerPsiField N ξ ω y *
        (hairerPsiWickSquare N ρ' ε' ξ' ω q.2 * hairerPsiField N ξ' ω y') ∂P =
      g q.1 * g' q.2 * isqBlockKernel (hairerCovariance N ρ ε)
        (hairerCrossCovarianceTwo N ρ ε ρ' ε') (hairerCovariance N ρ' ε')
        (hairerCrossCovarianceTwo N ρ ε ρ' ε') (hairerCrossCovarianceTwo N ρ ε ρ' ε')
        (hairerCrossCovarianceTwo N ρ ε ρ' ε') q.1 y q.2 y' :=
    fun q => by rw [(hdata q).2.2]
  simp only [hpt] at hfub hexp
  rw [hfub]
  exact integral_prod _ hexp

/-- **Two-scale, two-mollifier covariance of `I₂Ψ`.** -/
theorem productISqPsiField_integral_mul_two_scale_cross (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hε : 0 < ε) (hε' : 0 < ε') (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (x x' y y' : SpaceTime) :
    ∫ ω, productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x' ω y' ∂P =
      ∫ w, ∫ w', hairerI2Psi2Kernel N x y w * hairerI2Psi2Kernel N x' y' w' *
        isqBlockKernel (hairerCovariance N ρ ε) (hairerCrossCovarianceTwo N ρ ε ρ' ε')
          (hairerCovariance N ρ' ε') (hairerCrossCovarianceTwo N ρ ε ρ' ε')
          (hairerCrossCovarianceTwo N ρ ε ρ' ε') (hairerCrossCovarianceTwo N ρ ε ρ' ε')
          w y w' y' := by
  have := hairerPsiWickSquare_testedPair_integral_cross N hρ hρ' hε hε' hW hξ hξ'
    (integrable_hairerI2Psi2Kernel N x y) (integrable_hairerI2Psi2Kernel N x' y') y y'
  simpa only [productISqPsiField] using this

end RegularityStructures.Phi43

end
