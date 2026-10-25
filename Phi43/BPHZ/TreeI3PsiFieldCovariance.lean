/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiField
public import Phi43.BPHZ.TreeI3PsiFieldFubini
public import Phi43.BPHZ.TreeI3PsiFieldMoment

/-!
# The covariance identity for `I₃Ψ`

For integrable kernels `g, ḡ`, scales `ε, ε'` and points `y, ȳ` the covariance of the fields
`(∫ g :Ψ_ε³:) Ψ_ε(y)` and `(∫ ḡ :Ψ_ε'³:) Ψ_ε'(ȳ)` is
`∫∫ g(w) ḡ(w̄) [18 Q_ε(w - y) Q_{εε'}(w - w̄)² Q_ε'(w̄ - ȳ) + 6 Q_{εε'}(w - w̄)³ Q_{εε'}(y - ȳ)
  + 18 Q_{εε'}(w - w̄)² Q_{εε'}(w - ȳ) Q_{εε'}(y - w̄)] dw dw̄`,
with `Q_{εε'} = hairerCrossCovariance` (orientation `Q_{εε'}(z - z') = E[Ψ_ε(z) Ψ_ε'(z')]`).  The
proof applies Fubini on `Ω × (SpaceTime × SpaceTime)` (`integral_testedPair_eq`), justified by the
moment bound `E|:X_a³: X_b :X_c³: X_d| ≤ 42 D⁴` on the four-point Gaussian vector
`(Ψ_ε(w), Ψ_ε(y), Ψ_ε'(w̄), Ψ_ε'(ȳ))`, and the block formula
`integral_wick_three_mul_X_mul_wick_three_mul_X`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The block pattern of `E[:X_a³: X_b :X_c³: X_d]` with the six covariance entries as separate
arguments: `18 C_ab C_ac² C_cd + 6 C_ac³ C_bd + 18 C_ac² C_ad C_bc`, evaluated at
`(a, b, c, d) = (w, y, w', y')`, so `C_ab = Cab (w - y)`, `C_ac = Cac (w - w')`, `C_cd = Ccd (w' - y')`,
`C_bd = Cbd (y - y')`, `C_ad = Cad (w - y')`, `C_bc = Cbc (y - w')`. -/
def i3PsiBlockKernel (Cab Cac Ccd Cbd Cad Cbc : SpaceTime → ℝ) (w y w' y' : SpaceTime) : ℝ :=
  18 * Cab (w - y) * Cac (w - w') ^ 2 * Ccd (w' - y') + 6 * Cac (w - w') ^ 3 * Cbd (y - y') +
    18 * Cac (w - w') ^ 2 * Cad (w - y') * Cbc (y - w')

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- The four-point Gaussian vector `(Ψ_ε(w), Ψ_ε(y), Ψ_ε'(w̄), Ψ_ε'(ȳ))`. -/
private theorem hairerPsiField_isCentredGaussianVector_four (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ ε' ξ') (w y w' y' : SpaceTime) :
    IsCentredGaussianVector P
      (fun ω (i : Fin 4) => hairerPsiField N (![ξ, ξ, ξ', ξ'] i) ω (![w, y, w', y'] i))
      (fun i j => hairerCrossCovariance N ρ (![ε, ε, ε', ε'] i) (![ε, ε, ε', ε'] j)
        (![w, y, w', y'] i - ![w, y, w', y'] j)) :=
  hairerPsiField_isCentredGaussianVector_multiscale N hρ (ε := ![ε, ε, ε', ε'])
    (ξ := ![ξ, ξ, ξ', ξ']) (fun i => by fin_cases i <;> simpa) hW
    (fun i => by fin_cases i <;> simpa) ![w, y, w', y']

/-- **Pointwise moment data for `:Ψ_ε³:(w) Ψ_ε(y) :Ψ_ε'³:(w̄) Ψ_ε'(ȳ)`**: integrability, the uniform
bound `E|·| ≤ 42 (max c_ε c_ε')⁴`, and the Wick-block formula for the expectation. -/
theorem hairerPsiWickCube_pair_data (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ ε' ξ') (w y w' y' : SpaceTime) :
    Integrable (fun ω => hairerPsiWickCubeField N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickCubeField N ρ ε' ξ' ω w' * hairerPsiField N ξ' ω y')) P ∧
    ∫ ω, |hairerPsiWickCubeField N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickCubeField N ρ ε' ξ' ω w' * hairerPsiField N ξ' ω y')| ∂P ≤
      42 * (max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ ε')) ^ 4 ∧
    ∫ ω, hairerPsiWickCubeField N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickCubeField N ρ ε' ξ' ω w' * hairerPsiField N ξ' ω y') ∂P =
      i3PsiBlockKernel (hairerCovariance N ρ ε) (hairerCrossCovariance N ρ ε ε')
        (hairerCovariance N ρ ε') (hairerCrossCovariance N ρ ε ε') (hairerCrossCovariance N ρ ε ε')
        (hairerCrossCovariance N ρ ε ε') w y w' y' := by
  have h := hairerPsiField_isCentredGaussianVector_four N hρ hε hε' hW hξ hξ' w y w' y'
  have hD : ∀ i, hairerCrossCovariance N ρ (![ε, ε, ε', ε'] i) (![ε, ε, ε', ε'] i)
      (![w, y, w', y'] i - ![w, y, w', y'] i) ≤
      max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ ε') := by
    intro i
    fin_cases i <;> simp [hairerCrossCovariance_self, ← hairerWickConstant_eq_covariance_zero]
  have hmom := h.integrable_and_abs_integral_wick_three_le hD 0 1 2 3
  have hform := integral_wick_three_mul_X_mul_wick_three_mul_X h 0 1 2 3
  have e : ∀ ω, hairerPsiWickCubeField N ρ ε ξ ω w * hairerPsiField N ξ ω y *
      (hairerPsiWickCubeField N ρ ε' ξ' ω w' * hairerPsiField N ξ' ω y') =
      wickMonomial (fun i j => hairerCrossCovariance N ρ (![ε, ε, ε', ε'] i)
        (![ε, ε, ε', ε'] j) (![w, y, w', y'] i - ![w, y, w', y'] j))
        (List.replicate 3 0) (fun i => hairerPsiField N (![ξ, ξ, ξ', ξ'] i) ω (![w, y, w', y'] i))
        * hairerPsiField N (![ξ, ξ, ξ', ξ'] 1) ω (![w, y, w', y'] 1) *
        wickMonomial (fun i j => hairerCrossCovariance N ρ (![ε, ε, ε', ε'] i)
        (![ε, ε, ε', ε'] j) (![w, y, w', y'] i - ![w, y, w', y'] j))
        (List.replicate 3 2) (fun i => hairerPsiField N (![ξ, ξ, ξ', ξ'] i) ω (![w, y, w', y'] i))
        * hairerPsiField N (![ξ, ξ, ξ', ξ'] 3) ω (![w, y, w', y'] 3) := by
    intro ω
    rw [show List.replicate 3 (0 : Fin 4) = [0, 0, 0] from rfl,
      show List.replicate 3 (2 : Fin 4) = [2, 2, 2] from rfl, wickMonomial_triple_self,
      wickMonomial_triple_self]
    simp [hairerPsiWickCubeField, hairerCrossCovariance_self,
      ← hairerWickConstant_eq_covariance_zero]
    ring
  simp only [e]
  refine ⟨hmom.1, hmom.2, ?_⟩
  rw [hform]
  simp [i3PsiBlockKernel, hairerCrossCovariance_self]

/-- **Covariance identity, general kernels.** For integrable `g, g'`,
`E[((∫ g :Ψ_ε³:) Ψ_ε(y)) ((∫ g' :Ψ_ε'³:) Ψ_ε'(ȳ))] =
  ∫∫ g(w) g'(w̄) i3PsiBlockKernel Q_ε Q_{εε'} Q_ε' Q_{εε'} Q_{εε'} Q_{εε'} w y w̄ ȳ dw dw̄`. -/
theorem hairerPsiWickCube_testedPair_integral (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ ε' ξ') {g g' : SpaceTime → ℝ} (hg : Integrable g)
    (hg' : Integrable g') (y y' : SpaceTime) :
    ∫ ω, ((∫ w, g w * hairerPsiWickCubeField N ρ ε ξ ω w) * hairerPsiField N ξ ω y) *
        ((∫ w, g' w * hairerPsiWickCubeField N ρ ε' ξ' ω w) * hairerPsiField N ξ' ω y') ∂P =
      ∫ w, ∫ w', g w * g' w' * i3PsiBlockKernel (hairerCovariance N ρ ε)
        (hairerCrossCovariance N ρ ε ε') (hairerCovariance N ρ ε') (hairerCrossCovariance N ρ ε ε')
        (hairerCrossCovariance N ρ ε ε') (hairerCrossCovariance N ρ ε ε') w y w' y' := by
  have := hW.isProbabilityMeasure
  have hdata := fun q : SpaceTime × SpaceTime =>
    hairerPsiWickCube_pair_data N hρ hε hε' hW hξ hξ' q.1 y q.2 y'
  have hY := measurable_hairerPsiWickCubeField_uncurry N hξ
  have hY' := measurable_hairerPsiWickCubeField_uncurry N hξ'
  have ha := measurable_hairerPsiField_apply N hξ y
  have hb := measurable_hairerPsiField_apply N hξ' y'
  have hi := fun q : SpaceTime × SpaceTime => (hdata q).1
  have hM := fun q : SpaceTime × SpaceTime => (hdata q).2.1
  have hfub := integral_testedPair_eq hY hY' ha hb hg hg' hi hM
  have hexp := integrable_testedPair_expectation hY hY' ha hb hg hg' hi hM
  have hpt : ∀ q : SpaceTime × SpaceTime, g q.1 * g' q.2 *
      ∫ ω, hairerPsiWickCubeField N ρ ε ξ ω q.1 * hairerPsiField N ξ ω y *
        (hairerPsiWickCubeField N ρ ε' ξ' ω q.2 * hairerPsiField N ξ' ω y') ∂P =
      g q.1 * g' q.2 * i3PsiBlockKernel (hairerCovariance N ρ ε)
        (hairerCrossCovariance N ρ ε ε') (hairerCovariance N ρ ε') (hairerCrossCovariance N ρ ε ε')
        (hairerCrossCovariance N ρ ε ε') (hairerCrossCovariance N ρ ε ε') q.1 y q.2 y' :=
    fun q => by rw [(hdata q).2.2]
  simp only [hpt] at hfub hexp
  rw [hfub]
  exact integral_prod _ hexp

end RegularityStructures.Phi43

end
