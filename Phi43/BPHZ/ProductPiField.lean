/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiFieldCovariance
public import Phi43.BPHZ.TreeI2Psi2TestedMoment
public import Phi43.BPHZ.ProductDiagramWick

/-!
# The field `I₂Ψ` of the tree `I(Ψ²)Ψ`: definition, measurability and the covariance identity

For a base point `x` set `I₂Ψ_x(y) = (∫ (K(y - w) - K(x - w)) :Ψ²:(w) dw) Ψ(y)`.  By the Wick block
`E[:X_a²: X_b :X_c²: X_d] = 2 C_ac² C_bd + 4 C_ac C_ad C_bc + 4 C_ab C_ac C_cd`
(`integral_wick_two_mul_X_mul_wick_two_mul_X`) and Fubini (`integral_testedPair_eq`), for integrable
kernels `g, g'` and scales `ε, ε'`
`E[((∫ g :Ψ_ε²:) Ψ_ε(y)) ((∫ g' :Ψ_ε'²:) Ψ_ε'(ȳ))] = ∫∫ g(w) g'(w̄) isqBlockKernel ... dw dw̄`
(`hairerPsiWickSquare_testedPair_integral`).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The field `I₂Ψ_x(y) = (∫ (K(y - w) - K(x - w)) :Ψ²:(w) dw) Ψ(y)`. -/
def productISqPsiField {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (x : SpaceTime) (ω : Ω) (y : SpaceTime) : ℝ :=
  (∫ w, hairerI2Psi2Kernel N x y w * hairerPsiWickSquare N ρ ε ξ ω w) * hairerPsiField N ξ ω y

/-- The block pattern of `E[:X_a²: X_b :X_c²: X_d]`, evaluated at `(a, b, c, d) = (w, y, w', y')`. -/
def isqBlockKernel (Cab Cac Ccd Cbd Cad Cbc : SpaceTime → ℝ) (w y w' y' : SpaceTime) : ℝ :=
  2 * Cac (w - w') ^ 2 * Cbd (y - y') + 4 * Cac (w - w') * Cad (w - y') * Cbc (y - w') +
    4 * Cab (w - y) * Cac (w - w') * Ccd (w' - y')

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- **Joint measurability of `I₂Ψ`.** -/
theorem measurable_productISqPsiField_uncurry (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x : SpaceTime) :
    Measurable (fun q : Ω × SpaceTime => productISqPsiField N ρ ε ξ x q.1 q.2) := by
  have hK := measurable_constantsComparison_hairerKernelTorus N
  have hY := measurable_hairerPsiWickSquare_uncurry N hξ
  have h1 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      hairerKernelTorus N (r.1.2 - r.2)) :=
    hK.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)
  have h2 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime => hairerKernelTorus N (x - r.2)) :=
    hK.comp (measurable_const.sub measurable_snd)
  have h3 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      hairerPsiWickSquare N ρ ε ξ r.1.1 r.2) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiWickSquare N ρ ε ξ q.1 q.2)
      (f := fun r : (Ω × SpaceTime) × SpaceTime => (r.1.1, r.2)) hY
      (measurable_fst.fst.prodMk measurable_snd)
  have hint : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      hairerI2Psi2Kernel N x r.1.2 r.2 * hairerPsiWickSquare N ρ ε ξ r.1.1 r.2) :=
    (h1.sub h2).mul h3
  have hI : Measurable (fun q : Ω × SpaceTime => ∫ w,
      hairerI2Psi2Kernel N x q.2 w * hairerPsiWickSquare N ρ ε ξ q.1 w) :=
    hint.stronglyMeasurable.integral_prod_right'.measurable
  exact hI.mul (measurable_hairerPsiField_uncurry N hξ)

private theorem hairerPsiField_isCentredGaussianVector_four' (N : ℕ) (hρ : IsMollifier ρ)
    (hε : 0 < ε) (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ ε' ξ') (w y w' y' : SpaceTime) :
    IsCentredGaussianVector P
      (fun ω (i : Fin 4) => hairerPsiField N (![ξ, ξ, ξ', ξ'] i) ω (![w, y, w', y'] i))
      (fun i j => hairerCrossCovariance N ρ (![ε, ε, ε', ε'] i) (![ε, ε, ε', ε'] j)
        (![w, y, w', y'] i - ![w, y, w', y'] j)) :=
  hairerPsiField_isCentredGaussianVector_multiscale N hρ (ε := ![ε, ε, ε', ε'])
    (ξ := ![ξ, ξ, ξ', ξ']) (fun i => by fin_cases i <;> simpa) hW
    (fun i => by fin_cases i <;> simpa) ![w, y, w', y']

/-- **Pointwise moment data for `:Ψ_ε²:(w) Ψ_ε(y) :Ψ_ε'²:(w̄) Ψ_ε'(ȳ)`**: integrability, the bound
`E|·| ≤ 10 (max c_ε c_ε')³`, and the Wick-block formula for the expectation. -/
theorem hairerPsiWickSquare_pair_data (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ ε' ξ') (w y w' y' : SpaceTime) :
    Integrable (fun ω => hairerPsiWickSquare N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickSquare N ρ ε' ξ' ω w' * hairerPsiField N ξ' ω y')) P ∧
    ∫ ω, |hairerPsiWickSquare N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickSquare N ρ ε' ξ' ω w' * hairerPsiField N ξ' ω y')| ∂P ≤
      10 * (max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ ε')) ^ 3 ∧
    ∫ ω, hairerPsiWickSquare N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickSquare N ρ ε' ξ' ω w' * hairerPsiField N ξ' ω y') ∂P =
      isqBlockKernel (hairerCovariance N ρ ε) (hairerCrossCovariance N ρ ε ε')
        (hairerCovariance N ρ ε') (hairerCrossCovariance N ρ ε ε') (hairerCrossCovariance N ρ ε ε')
        (hairerCrossCovariance N ρ ε ε') w y w' y' := by
  have h := hairerPsiField_isCentredGaussianVector_four' N hρ hε hε' hW hξ hξ' w y w' y'
  have hD : ∀ i, hairerCrossCovariance N ρ (![ε, ε, ε', ε'] i) (![ε, ε, ε', ε'] i)
      (![w, y, w', y'] i - ![w, y, w', y'] i) ≤
      max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ ε') := by
    intro i
    fin_cases i <;> simp [hairerCrossCovariance_self, ← hairerWickConstant_eq_covariance_zero]
  have hmom := h.integrable_and_abs_integral_wick_two_le hD 0 1 2 3
  have hform := integral_wick_two_mul_X_mul_wick_two_mul_X h 0 1 2 3
  have e : ∀ ω, hairerPsiWickSquare N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickSquare N ρ ε' ξ' ω w' * hairerPsiField N ξ' ω y') =
      wickMonomial (fun i j => hairerCrossCovariance N ρ (![ε, ε, ε', ε'] i)
        (![ε, ε, ε', ε'] j) (![w, y, w', y'] i - ![w, y, w', y'] j))
        (List.replicate 2 0) (fun i => hairerPsiField N (![ξ, ξ, ξ', ξ'] i) ω (![w, y, w', y'] i))
        * hairerPsiField N (![ξ, ξ, ξ', ξ'] 1) ω (![w, y, w', y'] 1) *
        wickMonomial (fun i j => hairerCrossCovariance N ρ (![ε, ε, ε', ε'] i)
        (![ε, ε, ε', ε'] j) (![w, y, w', y'] i - ![w, y, w', y'] j))
        (List.replicate 2 2) (fun i => hairerPsiField N (![ξ, ξ, ξ', ξ'] i) ω (![w, y, w', y'] i))
        * hairerPsiField N (![ξ, ξ, ξ', ξ'] 3) ω (![w, y, w', y'] 3) := by
    intro ω
    rw [show List.replicate 2 (0 : Fin 4) = [0, 0] from rfl,
      show List.replicate 2 (2 : Fin 4) = [2, 2] from rfl, wickMonomial_pair_self,
      wickMonomial_pair_self]
    simp [hairerPsiWickSquare, hairerCrossCovariance_self,
      ← hairerWickConstant_eq_covariance_zero]
    ring
  simp only [e]
  refine ⟨hmom.1, hmom.2, ?_⟩
  rw [hform]
  simp [isqBlockKernel, hairerCrossCovariance_self]

/-- **Covariance identity, general kernels.** -/
theorem hairerPsiWickSquare_testedPair_integral (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ ε' ξ') {g g' : SpaceTime → ℝ} (hg : Integrable g)
    (hg' : Integrable g') (y y' : SpaceTime) :
    ∫ ω, ((∫ w, g w * hairerPsiWickSquare N ρ ε ξ ω w) * hairerPsiField N ξ ω y) *
        ((∫ w, g' w * hairerPsiWickSquare N ρ ε' ξ' ω w) * hairerPsiField N ξ' ω y') ∂P =
      ∫ w, ∫ w', g w * g' w' * isqBlockKernel (hairerCovariance N ρ ε)
        (hairerCrossCovariance N ρ ε ε') (hairerCovariance N ρ ε') (hairerCrossCovariance N ρ ε ε')
        (hairerCrossCovariance N ρ ε ε') (hairerCrossCovariance N ρ ε ε') w y w' y' := by
  have := hW.isProbabilityMeasure
  have hdata := fun q : SpaceTime × SpaceTime =>
    hairerPsiWickSquare_pair_data N hρ hε hε' hW hξ hξ' q.1 y q.2 y'
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
        (hairerPsiWickSquare N ρ ε' ξ' ω q.2 * hairerPsiField N ξ' ω y') ∂P =
      g q.1 * g' q.2 * isqBlockKernel (hairerCovariance N ρ ε)
        (hairerCrossCovariance N ρ ε ε') (hairerCovariance N ρ ε') (hairerCrossCovariance N ρ ε ε')
        (hairerCrossCovariance N ρ ε ε') (hairerCrossCovariance N ρ ε ε') q.1 y q.2 y' :=
    fun q => by rw [(hdata q).2.2]
  simp only [hpt] at hfub hexp
  rw [hfub]
  exact integral_prod _ hexp

/-- **Two-scale covariance of `I₂Ψ`.** -/
theorem productISqPsiField_integral_mul_two_scale (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ ε' ξ') (x x' y y' : SpaceTime) :
    ∫ ω, productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε' ξ' x' ω y' ∂P =
      ∫ w, ∫ w', hairerI2Psi2Kernel N x y w * hairerI2Psi2Kernel N x' y' w' *
        isqBlockKernel (hairerCovariance N ρ ε) (hairerCrossCovariance N ρ ε ε')
          (hairerCovariance N ρ ε') (hairerCrossCovariance N ρ ε ε')
          (hairerCrossCovariance N ρ ε ε') (hairerCrossCovariance N ρ ε ε') w y w' y' := by
  have := hairerPsiWickSquare_testedPair_integral N hρ hε hε' hW hξ hξ'
    (integrable_hairerI2Psi2Kernel N x y) (integrable_hairerI2Psi2Kernel N x' y') y y'
  simpa only [productISqPsiField] using this

end RegularityStructures.Phi43

end
