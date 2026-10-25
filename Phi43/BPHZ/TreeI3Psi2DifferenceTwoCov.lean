/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DifferenceTwoCross
public import Phi43.BPHZ.CrossMollifierPsi

/-!
# The tree `I(Ψ³) Ψ²`: cross covariance of the fields at two mollifiers

For fields `F_a(y) = hairerI3Psi2Field N ρ ε ξ x ·` and `F_b = hairerI3Psi2Field N ρ' ε' ξ' x ·` built
from noises `ξ`, `ξ'` of the same white noise regularised with `(ρ, ε)`, `(ρ', ε')`,
`E[F_a(y) F_b(y')]` is the sum of the chaos-`5`, `3`, `1` double integrals, minus the two cross terms
with the counterterm `-3 C₂ Ψ`, plus `9 C₂^a C₂^b Q_{ab}(y - y')`
(`hairerI3Psi2Field_integral_mulTwo`), and the covariance of the difference of the fields is the
second difference of these (`hairerI3Psi2Field_sub_integral_mulTwo`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The covariance `E[F_a(y) F_b(y')]` of the fields `hairerI3Psi2Field` at `(ρ, ε)`, `(ρ', ε')`. -/
def hairerI3Psi2CovTwo (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (x : SpaceTime) (ε ε' : ℝ)
    (y y' : SpaceTime) : ℝ :=
  (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
    hairerI3Psi2Chaos5Two N ![ρ, ρ, ρ', ρ'] ![ε, ε, ε', ε'] y y' q.1 q.2) +
  (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
    hairerI3Psi2Chaos3Two N ![ρ, ρ, ρ', ρ'] ![ε, ε, ε', ε'] y y' q.1 q.2) +
  (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
    hairerI3Psi2Chaos1Two N ![ρ, ρ, ρ', ρ'] ![ε, ε, ε', ε'] y y' q.1 q.2) -
  3 * hairerSunsetConstant N ρ' ε' *
    (∫ w, hairerI2Psi2Kernel N x y w *
      hairerI3Psi2CrossKernelTwo N ![ρ, ρ, ρ'] ![ε, ε, ε'] y y' w) -
  3 * hairerSunsetConstant N ρ ε *
    (∫ w, hairerI2Psi2Kernel N x y' w *
      hairerI3Psi2CrossKernelTwo N ![ρ', ρ', ρ] ![ε', ε', ε] y' y w) +
  9 * hairerSunsetConstant N ρ ε * hairerSunsetConstant N ρ' ε' *
    hairerCrossCovarianceTwo N ρ ε ρ' ε' (y - y')

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- `E[Ψ_a(y) Ψ_b(y')] = Q_{ab}(y - y')`, with integrability of the product. -/
theorem integral_hairerPsiField_mul_crossTwo (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {a b : ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (ha : 0 < a) (hb : 0 < b)
    (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ' b ξ') (y y' : SpaceTime) :
    Integrable (fun ω => hairerPsiField N ξ ω y * hairerPsiField N ξ' ω y') P ∧
      ∫ ω, hairerPsiField N ξ ω y * hairerPsiField N ξ' ω y' ∂P =
        hairerCrossCovarianceTwo N ρ a ρ' b (y - y') := by
  have h := hairerPsiField_isCentredGaussianVector_two_mollifier N hρ hρ' ha hb hW hξ hξ' y y'
  have h1 := h.integrable_mul 0 1
  have h2 := h.integral_mul 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  exact ⟨h1, h2⟩

private theorem integral_four_terms_two {T₁ T₂ T₃ T₄ : Ω → ℝ} [IsProbabilityMeasure P]
    (h₁ : Integrable T₁ P) (h₂ : Integrable T₂ P) (h₃ : Integrable T₃ P) (h₄ : Integrable T₄ P)
    (ka kb : ℝ) :
    Integrable (fun ω => T₁ ω - kb * T₂ ω - ka * T₃ ω + ka * kb * T₄ ω) P ∧
      ∫ ω, (T₁ ω - kb * T₂ ω - ka * T₃ ω + ka * kb * T₄ ω) ∂P =
        ∫ ω, T₁ ω ∂P - kb * ∫ ω, T₂ ω ∂P - ka * ∫ ω, T₃ ω ∂P + ka * kb * ∫ ω, T₄ ω ∂P := by
  have j1 : Integrable (fun ω => T₁ ω - kb * T₂ ω) P := h₁.sub (h₂.const_mul kb)
  have j2 : Integrable (fun ω => T₁ ω - kb * T₂ ω - ka * T₃ ω) P := j1.sub (h₃.const_mul ka)
  refine ⟨j2.add (h₄.const_mul _), ?_⟩
  rw [integral_add j2 (h₄.const_mul _), integral_sub j1 (h₃.const_mul ka),
    integral_sub h₁ (h₂.const_mul kb), integral_const_mul, integral_const_mul, integral_const_mul]

/-- The four-argument identity with scales `(a, a, b, b)`, mollifiers `(ρ, ρ, ρ', ρ')`. -/
private theorem hairerI3Psi2_integral_mul_two_mollifier (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    {a b : ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (ha : 0 < a) (hb : 0 < b)
    (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ' b ξ')
    {g₁ g₃ : SpaceTime → ℝ} (hg₁ : Integrable g₁) (hg₃ : Integrable g₃) (y y' : SpaceTime) :
    Integrable (fun ω => ((∫ w, g₁ w * hairerPsiWickCube N ρ a ξ ω w) *
        hairerPsiWickSquare N ρ a ξ ω y) * ((∫ w, g₃ w * hairerPsiWickCube N ρ' b ξ' ω w) *
          hairerPsiWickSquare N ρ' b ξ' ω y')) P ∧
    ∫ ω, ((∫ w, g₁ w * hairerPsiWickCube N ρ a ξ ω w) * hairerPsiWickSquare N ρ a ξ ω y) *
        ((∫ w, g₃ w * hairerPsiWickCube N ρ' b ξ' ω w) *
          hairerPsiWickSquare N ρ' b ξ' ω y') ∂P =
      (∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI3Psi2Chaos5Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2) +
      (∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI3Psi2Chaos3Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2) +
      ∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI3Psi2Chaos1Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2 := by
  have hρs : ∀ i, IsMollifier ((![ρ, ρ, ρ', ρ'] : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) i) := by
    intro i
    fin_cases i <;> simpa
  have hε : ∀ i, 0 < (![a, a, b, b] : Fin 4 → ℝ) i := by
    intro i
    fin_cases i <;> simpa
  have hξs : ∀ i, IsRegularisedNoise P W ((![ρ, ρ, ρ', ρ'] : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) i)
      ((![a, a, b, b] : Fin 4 → ℝ) i) ((![ξ, ξ, ξ', ξ'] : Fin 4 → Ω → SpaceTime → ℝ) i) := by
    intro i
    fin_cases i <;> simpa
  have h := hairerI3Psi2_integral_mul_four_two N hρs hε hW hξs hg₁ hg₃ y y'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨by simpa only [mul_assoc] using h1, by simpa only [mul_assoc] using h2⟩

/-- The cross identity with mollifiers `(ρ, ρ, ρ')`, noises `(ξ, ξ, ξ')`. -/
private theorem hairerI3Psi2_integral_cross_two_mollifier (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    {a b : ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (ha : 0 < a) (hb : 0 < b)
    (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ' b ξ')
    {g : SpaceTime → ℝ} (hg : Integrable g) (y y' : SpaceTime) :
    Integrable (fun ω => (∫ w, g w * hairerPsiWickCube N ρ a ξ ω w) *
      hairerPsiWickSquare N ρ a ξ ω y * hairerPsiField N ξ' ω y') P ∧
    ∫ ω, (∫ w, g w * hairerPsiWickCube N ρ a ξ ω w) * hairerPsiWickSquare N ρ a ξ ω y *
      hairerPsiField N ξ' ω y' ∂P =
        ∫ w, g w * hairerI3Psi2CrossKernelTwo N ![ρ, ρ, ρ'] ![a, a, b] y y' w := by
  have hρs : ∀ i, IsMollifier ((![ρ, ρ, ρ'] : Fin 3 → ℝ × (Fin 3 → ℝ) → ℝ) i) := by
    intro i
    fin_cases i <;> simpa
  have hε : ∀ i, 0 < (![a, a, b] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> simpa
  have hξs : ∀ i, IsRegularisedNoise P W ((![ρ, ρ, ρ'] : Fin 3 → ℝ × (Fin 3 → ℝ) → ℝ) i)
      ((![a, a, b] : Fin 3 → ℝ) i) ((![ξ, ξ, ξ'] : Fin 3 → Ω → SpaceTime → ℝ) i) := by
    intro i
    fin_cases i <;> simpa
  have h := integral_integral_mul_hairerPsiWickCube_square_fieldTwo N hρs hε hW hξs hg y y'
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] using h

/-- **Covariance of the fields `hairerI3Psi2Field` at two mollifiers** [Hai14, p. 170-171]. -/
theorem hairerI3Psi2Field_integral_mulTwo (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {a b : ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (ha : 0 < a) (hb : 0 < b)
    (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ' b ξ')
    (x y y' : SpaceTime) :
    Integrable (fun ω => hairerI3Psi2Field N ρ a ξ x ω y * hairerI3Psi2Field N ρ' b ξ' x ω y') P ∧
    ∫ ω, hairerI3Psi2Field N ρ a ξ x ω y * hairerI3Psi2Field N ρ' b ξ' x ω y' ∂P =
      hairerI3Psi2CovTwo N ρ ρ' x a b y y' := by
  have hprob := hW.isProbabilityMeasure
  have hg₁ := integrable_hairerI2Psi2Kernel N x y
  have hg₃ := integrable_hairerI2Psi2Kernel N x y'
  obtain ⟨i1, e1⟩ := hairerI3Psi2_integral_mul_two_mollifier N hρ hρ' ha hb hW hξ hξ' hg₁ hg₃ y y'
  obtain ⟨i2, e2⟩ := hairerI3Psi2_integral_cross_two_mollifier N hρ hρ' ha hb hW hξ hξ' hg₁ y y'
  obtain ⟨i3, e3⟩ := hairerI3Psi2_integral_cross_two_mollifier N hρ' hρ hb ha hW hξ' hξ hg₃ y' y
  obtain ⟨i4, e4⟩ := integral_hairerPsiField_mul_crossTwo N hρ hρ' ha hb hW hξ hξ' y y'
  obtain ⟨hint, hcov⟩ := integral_four_terms_two i1 i2
    (T₃ := fun ω => (∫ w, hairerI2Psi2Kernel N x y' w * hairerPsiWickCube N ρ' b ξ' ω w) *
      hairerPsiWickSquare N ρ' b ξ' ω y' * hairerPsiField N ξ ω y) i3 i4
    (3 * hairerSunsetConstant N ρ a) (3 * hairerSunsetConstant N ρ' b)
  have hpt : ∀ ω, hairerI3Psi2Field N ρ a ξ x ω y * hairerI3Psi2Field N ρ' b ξ' x ω y' =
      ((∫ w, hairerI2Psi2Kernel N x y w * hairerPsiWickCube N ρ a ξ ω w) *
          hairerPsiWickSquare N ρ a ξ ω y) *
        ((∫ w, hairerI2Psi2Kernel N x y' w * hairerPsiWickCube N ρ' b ξ' ω w) *
          hairerPsiWickSquare N ρ' b ξ' ω y') -
      3 * hairerSunsetConstant N ρ' b *
        ((∫ w, hairerI2Psi2Kernel N x y w * hairerPsiWickCube N ρ a ξ ω w) *
          hairerPsiWickSquare N ρ a ξ ω y * hairerPsiField N ξ' ω y') -
      3 * hairerSunsetConstant N ρ a *
        ((∫ w, hairerI2Psi2Kernel N x y' w * hairerPsiWickCube N ρ' b ξ' ω w) *
          hairerPsiWickSquare N ρ' b ξ' ω y' * hairerPsiField N ξ ω y) +
      3 * hairerSunsetConstant N ρ a * (3 * hairerSunsetConstant N ρ' b) *
        (hairerPsiField N ξ ω y * hairerPsiField N ξ' ω y') := fun ω => by
    unfold hairerI3Psi2Field
    ring
  simp_rw [hpt]
  refine ⟨hint, ?_⟩
  rw [hcov, e1, e2, e3, e4]
  unfold hairerI3Psi2CovTwo
  ring

/-- **Covariance of the difference of the fields `hairerI3Psi2Field` at two mollifiers.** -/
theorem hairerI3Psi2Field_sub_integral_mulTwo (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {a b : ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (ha : 0 < a) (hb : 0 < b)
    (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ' b ξ')
    (x y y' : SpaceTime) :
    Integrable (fun ω => (hairerI3Psi2Field N ρ a ξ x ω y - hairerI3Psi2Field N ρ' b ξ' x ω y) *
      (hairerI3Psi2Field N ρ a ξ x ω y' - hairerI3Psi2Field N ρ' b ξ' x ω y')) P ∧
    ∫ ω, (hairerI3Psi2Field N ρ a ξ x ω y - hairerI3Psi2Field N ρ' b ξ' x ω y) *
        (hairerI3Psi2Field N ρ a ξ x ω y' - hairerI3Psi2Field N ρ' b ξ' x ω y') ∂P =
      hairerI3Psi2CovTwo N ρ ρ x a a y y' - hairerI3Psi2CovTwo N ρ ρ' x a b y y' -
        hairerI3Psi2CovTwo N ρ' ρ x b a y y' + hairerI3Psi2CovTwo N ρ' ρ' x b b y y' := by
  obtain ⟨i1, e1⟩ := hairerI3Psi2Field_integral_mulTwo N hρ hρ ha ha hW hξ hξ x y y'
  obtain ⟨i2, e2⟩ := hairerI3Psi2Field_integral_mulTwo N hρ hρ' ha hb hW hξ hξ' x y y'
  obtain ⟨i3, e3⟩ := hairerI3Psi2Field_integral_mulTwo N hρ' hρ hb ha hW hξ' hξ x y y'
  obtain ⟨i4, e4⟩ := hairerI3Psi2Field_integral_mulTwo N hρ' hρ' hb hb hW hξ' hξ' x y y'
  have hpt : ∀ ω, (hairerI3Psi2Field N ρ a ξ x ω y - hairerI3Psi2Field N ρ' b ξ' x ω y) *
      (hairerI3Psi2Field N ρ a ξ x ω y' - hairerI3Psi2Field N ρ' b ξ' x ω y') =
      hairerI3Psi2Field N ρ a ξ x ω y * hairerI3Psi2Field N ρ a ξ x ω y' -
        hairerI3Psi2Field N ρ a ξ x ω y * hairerI3Psi2Field N ρ' b ξ' x ω y' -
        hairerI3Psi2Field N ρ' b ξ' x ω y * hairerI3Psi2Field N ρ a ξ x ω y' +
        hairerI3Psi2Field N ρ' b ξ' x ω y * hairerI3Psi2Field N ρ' b ξ' x ω y' :=
    fun ω => by ring
  have j1 : Integrable (fun ω => hairerI3Psi2Field N ρ a ξ x ω y *
      hairerI3Psi2Field N ρ a ξ x ω y' - hairerI3Psi2Field N ρ a ξ x ω y *
      hairerI3Psi2Field N ρ' b ξ' x ω y') P := i1.sub i2
  have j2 : Integrable (fun ω => hairerI3Psi2Field N ρ a ξ x ω y *
      hairerI3Psi2Field N ρ a ξ x ω y' - hairerI3Psi2Field N ρ a ξ x ω y *
      hairerI3Psi2Field N ρ' b ξ' x ω y' - hairerI3Psi2Field N ρ' b ξ' x ω y *
      hairerI3Psi2Field N ρ a ξ x ω y') P := j1.sub i3
  simp_rw [hpt]
  refine ⟨j2.add i4, ?_⟩
  rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2, e1, e2, e3, e4]

end RegularityStructures.Phi43

end
