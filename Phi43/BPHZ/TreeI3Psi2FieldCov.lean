/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2FieldChaos
public import Phi43.BPHZ.TreeI3Psi2FieldCross

/-!
# The tree `I(Ψ³) Ψ²`: covariance of the field

Let `F_a(y) = hairerI3Psi2Field N ρ a ξ x · y` be the field at scale `a`.  For scales `a`, `b`
(two noises `ξ`, `ξ'` of the same white noise) and points `y`, `y'`, with `δK_y(w) = K(y - w) -
K(x - w)` and `C₂^a = hairerSunsetConstant N ρ a`,
`E[F_a(y) F_b(y')] = ∫∫ δK_y δK_{y'} χ₅ + ∫∫ δK_y δK_{y'} χ₃ + ∫∫ δK_y δK_{y'} χ₁`
`  - 3 C₂^b ∫ δK_y(w) 6 Q_a(w - y)² Q_{ab}(w - y') dw`
`  - 3 C₂^a ∫ δK_{y'}(w') 6 Q_b(w' - y')² Q_{ba}(w' - y) dw'`
`  + 9 C₂^a C₂^b Q_{ab}(y - y')`,
the first three terms being the chaos-`5`, `3`, `1` kernels of the main product
`E[(∫ δK_y :Ψ³_a:) :Ψ²_a:(y) (∫ δK_{y'} :Ψ³_b:) :Ψ²_b:(y')]` (`TreeI3Psi2FieldChaos`) and the last
three terms (chaos `1`) the cross terms with `-3 C₂ Ψ` (`TreeI3Psi2FieldCross`, and
`E[Ψ_a(y) Ψ_b(y')] = Q_{ab}(y - y')`) [Hai14, p. 170-171].
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- `E[Ψ_a(y) Ψ_b(y')] = Q_{ab}(y - y')`, with integrability of the product. -/
theorem integral_hairerPsiField_mul_cross (N : ℕ) (hρ : IsMollifier ρ) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ b ξ')
    (y y' : SpaceTime) :
    Integrable (fun ω => hairerPsiField N ξ ω y * hairerPsiField N ξ' ω y') P ∧
      ∫ ω, hairerPsiField N ξ ω y * hairerPsiField N ξ' ω y' ∂P =
        hairerCrossCovariance N ρ a b (y - y') := by
  have h := hairerPsiField_isCentredGaussianVector_two_scale N hρ ha hb hW hξ hξ' y y'
  have h1 := h.integrable_mul 0 1
  have h2 := h.integral_mul 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  exact ⟨h1, h2⟩

/-- Algebra of the covariance of two fields `T₁ - κ_a T₂`-type products. -/
private theorem integral_four_terms {T₁ T₂ T₃ T₄ : Ω → ℝ} [IsProbabilityMeasure P]
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

/-- The four-argument identity with scales `(a, a, b, b)`, in the product form `(U V) (U' V')`. -/
private theorem hairerI3Psi2_integral_mul_two_scale (N : ℕ) (hρ : IsMollifier ρ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ b ξ')
    {g₁ g₃ : SpaceTime → ℝ} (hg₁ : Integrable g₁) (hg₃ : Integrable g₃) (y y' : SpaceTime) :
    Integrable (fun ω => ((∫ w, g₁ w * hairerPsiWickCube N ρ a ξ ω w) *
        hairerPsiWickSquare N ρ a ξ ω y) * ((∫ w, g₃ w * hairerPsiWickCube N ρ b ξ' ω w) *
          hairerPsiWickSquare N ρ b ξ' ω y')) P ∧
    ∫ ω, ((∫ w, g₁ w * hairerPsiWickCube N ρ a ξ ω w) * hairerPsiWickSquare N ρ a ξ ω y) *
        ((∫ w, g₃ w * hairerPsiWickCube N ρ b ξ' ω w) *
          hairerPsiWickSquare N ρ b ξ' ω y') ∂P =
      (∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI3Psi2Chaos5 N ρ a a b b y y' q.1 q.2) +
      (∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI3Psi2Chaos3 N ρ a a b b y y' q.1 q.2) +
      ∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI3Psi2Chaos1 N ρ a a b b y y' q.1 q.2 := by
  have hε : ∀ i, 0 < (![a, a, b, b] : Fin 4 → ℝ) i := by
    intro i
    fin_cases i <;> simpa
  have hξs : ∀ i, IsRegularisedNoise P W ρ ((![a, a, b, b] : Fin 4 → ℝ) i)
      ((![ξ, ξ, ξ', ξ'] : Fin 4 → Ω → SpaceTime → ℝ) i) := by
    intro i
    fin_cases i <;> simpa
  have h := hairerI3Psi2_integral_mul_four N hρ hε hW hξs hg₁ hg₃ y y'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨by simpa only [mul_assoc] using h1, by simpa only [mul_assoc] using h2⟩

/-- The cross identity with scales `(a, a, b)`, noises `(ξ, ξ, ξ')`. -/
private theorem hairerI3Psi2_integral_cross_two_scale (N : ℕ) (hρ : IsMollifier ρ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ b ξ')
    {g : SpaceTime → ℝ} (hg : Integrable g) (y y' : SpaceTime) :
    Integrable (fun ω => (∫ w, g w * hairerPsiWickCube N ρ a ξ ω w) *
      hairerPsiWickSquare N ρ a ξ ω y * hairerPsiField N ξ' ω y') P ∧
    ∫ ω, (∫ w, g w * hairerPsiWickCube N ρ a ξ ω w) * hairerPsiWickSquare N ρ a ξ ω y *
      hairerPsiField N ξ' ω y' ∂P =
        ∫ w, g w * hairerI3Psi2CrossKernel N ρ a a b y y' w := by
  have hε : ∀ i, 0 < (![a, a, b] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> simpa
  have hξs : ∀ i, IsRegularisedNoise P W ρ ((![a, a, b] : Fin 3 → ℝ) i)
      ((![ξ, ξ, ξ'] : Fin 3 → Ω → SpaceTime → ℝ) i) := by
    intro i
    fin_cases i <;> simpa
  have h := integral_integral_mul_hairerPsiWickCube_square_field N hρ hε hW hξs hg y y'
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] using h

/-- **Covariance of the field `hairerI3Psi2Field` of the tree `I(Ψ³) Ψ²`, two scales and four
arguments** [Hai14, p. 170-171]. For scales `a`, `b`, noises `ξ`, `ξ'` of the same white noise, a
base point `x` and points `y`, `y'`, `E[F_a(y) F_b(y')]` is the sum of the chaos-`5`, `3`, `1`
double integrals of `δK_y(w) δK_{y'}(w')` against `χ₅, χ₃, χ₁`, minus the two cross terms with
`-3 C₂ Ψ`, plus `9 C₂^a C₂^b Q_{ab}(y - y')`.  The field product is integrable. -/
theorem hairerI3Psi2Field_integral_mul (N : ℕ) (hρ : IsMollifier ρ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ b ξ')
    (x y y' : SpaceTime) :
    Integrable (fun ω => hairerI3Psi2Field N ρ a ξ x ω y * hairerI3Psi2Field N ρ b ξ' x ω y') P ∧
    ∫ ω, hairerI3Psi2Field N ρ a ξ x ω y * hairerI3Psi2Field N ρ b ξ' x ω y' ∂P =
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI3Psi2Chaos5 N ρ a a b b y y' q.1 q.2) +
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI3Psi2Chaos3 N ρ a a b b y y' q.1 q.2) +
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI3Psi2Chaos1 N ρ a a b b y y' q.1 q.2) -
      3 * hairerSunsetConstant N ρ b *
        (∫ w, hairerI2Psi2Kernel N x y w * hairerI3Psi2CrossKernel N ρ a a b y y' w) -
      3 * hairerSunsetConstant N ρ a *
        (∫ w, hairerI2Psi2Kernel N x y' w * hairerI3Psi2CrossKernel N ρ b b a y' y w) +
      9 * hairerSunsetConstant N ρ a * hairerSunsetConstant N ρ b *
        hairerCrossCovariance N ρ a b (y - y') := by
  have hprob := hW.isProbabilityMeasure
  have hg₁ := integrable_hairerI2Psi2Kernel N x y
  have hg₃ := integrable_hairerI2Psi2Kernel N x y'
  obtain ⟨i1, e1⟩ := hairerI3Psi2_integral_mul_two_scale N hρ ha hb hW hξ hξ' hg₁ hg₃ y y'
  obtain ⟨i2, e2⟩ := hairerI3Psi2_integral_cross_two_scale N hρ ha hb hW hξ hξ' hg₁ y y'
  obtain ⟨i3, e3⟩ := hairerI3Psi2_integral_cross_two_scale N hρ hb ha hW hξ' hξ hg₃ y' y
  obtain ⟨i4, e4⟩ := integral_hairerPsiField_mul_cross N hρ ha hb hW hξ hξ' y y'
  obtain ⟨hint, hcov⟩ := integral_four_terms i1 i2
    (T₃ := fun ω => (∫ w, hairerI2Psi2Kernel N x y' w * hairerPsiWickCube N ρ b ξ' ω w) *
      hairerPsiWickSquare N ρ b ξ' ω y' * hairerPsiField N ξ ω y) i3 i4
    (3 * hairerSunsetConstant N ρ a) (3 * hairerSunsetConstant N ρ b)
  have hpt : ∀ ω, hairerI3Psi2Field N ρ a ξ x ω y * hairerI3Psi2Field N ρ b ξ' x ω y' =
      ((∫ w, hairerI2Psi2Kernel N x y w * hairerPsiWickCube N ρ a ξ ω w) *
          hairerPsiWickSquare N ρ a ξ ω y) *
        ((∫ w, hairerI2Psi2Kernel N x y' w * hairerPsiWickCube N ρ b ξ' ω w) *
          hairerPsiWickSquare N ρ b ξ' ω y') -
      3 * hairerSunsetConstant N ρ b *
        ((∫ w, hairerI2Psi2Kernel N x y w * hairerPsiWickCube N ρ a ξ ω w) *
          hairerPsiWickSquare N ρ a ξ ω y * hairerPsiField N ξ' ω y') -
      3 * hairerSunsetConstant N ρ a *
        ((∫ w, hairerI2Psi2Kernel N x y' w * hairerPsiWickCube N ρ b ξ' ω w) *
          hairerPsiWickSquare N ρ b ξ' ω y' * hairerPsiField N ξ ω y) +
      3 * hairerSunsetConstant N ρ a * (3 * hairerSunsetConstant N ρ b) *
        (hairerPsiField N ξ ω y * hairerPsiField N ξ' ω y') := fun ω => by
    unfold hairerI3Psi2Field
    ring
  simp_rw [hpt]
  refine ⟨hint, ?_⟩
  rw [hcov, e1, e2, e3, e4]
  ring

end RegularityStructures.Phi43

end
