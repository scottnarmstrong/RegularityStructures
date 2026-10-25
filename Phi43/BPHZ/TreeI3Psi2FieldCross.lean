/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2FieldMean
public import Phi43.BPHZ.TreeI3Psi2FieldMoment
public import Phi43.BPHZ.TreeWickSquareFour
public import RegularityStructures.BPHZ.GaussianWickBlocksThree

/-!
# The tree `I(Ψ³) Ψ²`: cross terms with the counterterm `-3 C₂ Ψ`

For scales `ε₀, ε₁, ε₂`, noises `ξ₀, ξ₁, ξ₂` and points `z₀, z₁, z₂`, the diagram formula (W5) for
the Gaussian vector `(Ψ_{εᵢ}(zᵢ))ᵢ` gives
`E[:Ψ³_{ε₀}:(z₀) :Ψ²_{ε₁}:(z₁) Ψ_{ε₂}(z₂)] = 6 Q_{ε₀ε₁}(z₀ - z₁)² Q_{ε₀ε₂}(z₀ - z₂)`.
By stochastic Fubini, for `g ∈ L¹`,
`E[(∫ g :Ψ³_{ε₀}:) :Ψ²_{ε₁}:(y) Ψ_{ε₂}(y')] = ∫ g(w) 6 Q_{ε₀ε₁}(w - y)² Q_{ε₀ε₂}(w - y') dw`
(`integral_integral_mul_hairerPsiWickCube_square_field`).  This is the chaos-`1` contribution of
the cross terms with `-3 C₂ Ψ` in the covariance of the field `hairerI3Psi2Field`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The chaos-`1` kernel `6 Q_{ε₀ε₁}(w - y)² Q_{ε₀ε₂}(w - y')` of
`E[:Ψ³_{ε₀}:(w) :Ψ²_{ε₁}:(y) Ψ_{ε₂}(y')]`. -/
def hairerI3Psi2CrossKernel (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ ε₁ ε₂ : ℝ)
    (y y' w : SpaceTime) : ℝ :=
  6 * hairerCrossCovariance N ρ ε₀ ε₁ (w - y) ^ 2 * hairerCrossCovariance N ρ ε₀ ε₂ (w - y')

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : Fin 3 → ℝ} {ξ : Fin 3 → Ω → SpaceTime → ℝ}

omit [MeasurableSpace Ω] in
/-- The product `:Ψ³: :Ψ²: Ψ` at three scales is a product of Wick monomials of the multiscale
vector. -/
theorem hairerWickCubeSquareField_eq_wickMonomial (N : ℕ) (z : Fin 3 → SpaceTime) (ω : Ω) :
    hairerPsiWickCube N ρ (ε 0) (ξ 0) ω (z 0) * hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω (z 1) *
        hairerPsiField N (ξ 2) ω (z 2) =
      wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b))
          (List.replicate 3 0) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b))
          (List.replicate 2 1) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        hairerPsiField N (ξ 2) ω (z 2) := by
  have c0 := hairerPsiWickCube_eq_wickMonomial_multiscale (ρ := ρ) N ε ξ z ω 0
  have s1 := hairerPsiWickSquare_eq_wickMonomial_multiscale (ρ := ρ) N ε ξ z ω 1
  rw [c0, s1]
  rfl

/-- **(W5) for the tree `Ψ`.**
`E[:Ψ³_{ε₀}:(z₀) :Ψ²_{ε₁}:(z₁) Ψ_{ε₂}(z₂)] = 6 Q_{ε₀ε₁}(z₀ - z₁)² Q_{ε₀ε₂}(z₀ - z₂)`. -/
theorem hairerPsiWickCubeSquareField_integral_mul (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (z : Fin 3 → SpaceTime) :
    ∫ ω, hairerPsiWickCube N ρ (ε 0) (ξ 0) ω (z 0) * hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω (z 1) *
        hairerPsiField N (ξ 2) ω (z 2) ∂P =
      6 * hairerCrossCovariance N ρ (ε 0) (ε 1) (z 0 - z 1) ^ 2 *
        hairerCrossCovariance N ρ (ε 0) (ε 2) (z 0 - z 2) := by
  have h := hairerPsiField_isCentredGaussianVector_multiscale N hρ hε hW hξ z
  have hw := integral_wick_three_mul_wick_two_mul_X h 0 1 2
  simp_rw [hairerWickCubeSquareField_eq_wickMonomial N z]
  exact hw

/-- The product `:Ψ³: :Ψ²: Ψ` at three scales is integrable. -/
theorem integrable_hairerPsiWickCubeSquareField (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (z : Fin 3 → SpaceTime) :
    Integrable (fun ω => hairerPsiWickCube N ρ (ε 0) (ξ 0) ω (z 0) *
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω (z 1) * hairerPsiField N (ξ 2) ω (z 2)) P := by
  have h := hairerPsiField_isCentredGaussianVector_multiscale N hρ hε hW hξ z
  have hi := h.integrable_prod_wickMonomial
    (L := ![List.replicate 3 0, List.replicate 2 1, [2]])
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, wickMonomial_singleton] at hi
  exact hi.congr (Filter.Eventually.of_forall fun ω =>
    (hairerWickCubeSquareField_eq_wickMonomial N z ω).symm)

private theorem abs_mul_mul_le_young (a b c : ℝ) :
    |a * b * c| ≤ (a ^ 4 + b ^ 4) / 4 + c ^ 2 / 2 := by
  have h1 : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have h2 : a ^ 2 * |c| ≤ (a ^ 4 + c ^ 2) / 2 := by
    nlinarith [sq_nonneg (a ^ 2 - |c|), sq_abs c]
  have h3 : b ^ 2 * |c| ≤ (b ^ 4 + c ^ 2) / 2 := by
    nlinarith [sq_nonneg (b ^ 2 - |c|), sq_abs c]
  calc |a * b * c| = |a * b| * |c| := abs_mul _ _
    _ ≤ (a ^ 2 + b ^ 2) / 2 * |c| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ _ := by nlinarith

/-- **Uniform first-moment bound** for `:Ψ³_{ε₀}:(w) :Ψ²_{ε₁}:(y) Ψ_{ε₂}(y')` in `w`. -/
theorem exists_integral_abs_hairerPsiWickCubeSquareField_le (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (y y' : SpaceTime) :
    ∃ M : ℝ, ∀ w : SpaceTime,
      ∫ ω, |hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w * hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y *
        hairerPsiField N (ξ 2) ω y'| ∂P ≤ M := by
  have hprob := hW.isProbabilityMeasure
  obtain ⟨A, -, hA⟩ := exists_integral_hairerPsiWickCube_pow_four_le (ρ := ρ) (P := P) (W := W)
  refine ⟨((A * (6 * hairerWickConstant N ρ (ε 0) ^ 3) ^ 2) +
    60 * hairerWickConstant N ρ (ε 1) ^ 4) / 4 + hairerCovariance N ρ (ε 2) 0 / 2,
    fun w => ?_⟩
  have i0 := integrable_hairerPsiWickCube_pow_four N hρ (hε 0) hW (hξ 0) w
  have i1 := integrable_hairerPsiWickSquare_pow_four N hρ (hε 1) hW (hξ 1) y
  have hL2 := hairerPsiField_memLp N hρ (hε 2) hW (hξ 2) y'
  have i2 : Integrable (fun ω => hairerPsiField N (ξ 2) ω y' * hairerPsiField N (ξ 2) ω y') P :=
    hL2.integrable_mul hL2
  have j01 : Integrable (fun ω => hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4) P := i0.add i1
  have hz := integrable_hairerPsiWickCubeSquareField N hρ hε hW hξ ![w, y, y']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hz
  calc _ ≤ ∫ ω, ((hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w ^ 4 +
          hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4) / 4 +
          (hairerPsiField N (ξ 2) ω y' * hairerPsiField N (ξ 2) ω y') / 2) ∂P :=
        integral_mono hz.abs ((j01.div_const 4).add (i2.div_const 2)) fun ω => by
          have := abs_mul_mul_le_young (hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w)
            (hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y) (hairerPsiField N (ξ 2) ω y')
          simp only [sq] at this ⊢
          linarith
    _ = (∫ ω, hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w ^ 4 ∂P +
          ∫ ω, hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4 ∂P) / 4 +
          (∫ ω, hairerPsiField N (ξ 2) ω y' * hairerPsiField N (ξ 2) ω y' ∂P) / 2 := by
        rw [integral_add (j01.div_const 4) (i2.div_const 2), integral_div, integral_div,
          integral_add i0 i1]
    _ ≤ _ := by
        rw [integral_hairerPsiWickSquare_pow_four N hρ (hε 1) hW (hξ 1) y,
          hairerPsiField_integral_mul N hρ (hε 2) hW (hξ 2) y' y', sub_self]
        have a0 := hA N hρ (hε 0) hW (hξ 0) w
        linarith

/-- **Fubini for the Wick cube against `:Ψ²:(y) Ψ(y')`** (the cross term with the counterterm):
`E[(∫ g :Ψ³_{ε₀}:) :Ψ²_{ε₁}:(y) Ψ_{ε₂}(y')] = ∫ g(w) 6 Q_{ε₀ε₁}(w - y)² Q_{ε₀ε₂}(w - y') dw`, and
the integrand on the left is integrable. -/
theorem integral_integral_mul_hairerPsiWickCube_square_field (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) {g : SpaceTime → ℝ} (hg : Integrable g)
    (y y' : SpaceTime) :
    Integrable (fun ω => (∫ w, g w * hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w) *
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y * hairerPsiField N (ξ 2) ω y') P ∧
    ∫ ω, (∫ w, g w * hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w) *
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y * hairerPsiField N (ξ 2) ω y' ∂P =
        ∫ w, g w * hairerI3Psi2CrossKernel N ρ (ε 0) (ε 1) (ε 2) y y' w := by
  have hprob := hW.isProbabilityMeasure
  have hYm := measurable_hairerPsiWickCube_uncurry N (hξ 0)
  have hA : Measurable fun ω => hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiWickSquare N ρ (ε 1) (ξ 1) q.1 q.2)
      (f := fun ω : Ω => (ω, y)) (measurable_hairerPsiWickSquare_uncurry N (hξ 1))
      (measurable_id.prodMk measurable_const)
  have hB : Measurable fun ω => hairerPsiField N (ξ 2) ω y' :=
    measurable_hairerPsiField_apply N (hξ 2) y'
  obtain ⟨M, hM⟩ := exists_integral_abs_hairerPsiWickCubeSquareField_le N hρ hε hW hξ y y'
  have hpt : ∀ ω w, hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w *
      (hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y * hairerPsiField N (ξ 2) ω y') =
      hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w * hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y *
        hairerPsiField N (ξ 2) ω y' := fun ω w => by ring
  obtain ⟨hi, he⟩ := integral_integral_mul_mul_swap_field (P := P) (Y := hairerPsiWickCube N ρ
    (ε 0) (ξ 0)) (B := fun ω => hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y *
      hairerPsiField N (ξ 2) ω y') hYm (hA.mul hB) hg
    (fun w => by
      have := integrable_hairerPsiWickCubeSquareField N hρ hε hW hξ ![w, y, y']
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at this
      exact this.congr (Filter.Eventually.of_forall fun ω => (hpt ω w).symm))
    (fun w => by
      simp only [hpt]
      exact hM w)
  refine ⟨hi.congr (Filter.Eventually.of_forall fun ω => by simp only [mul_assoc]), ?_⟩
  simp only [mul_assoc] at he ⊢
  rw [he]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  congr 1
  have := hairerPsiWickCubeSquareField_integral_mul N hρ hε hW hξ ![w, y, y']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at this
  simp_rw [← mul_assoc]
  rw [this]
  rfl

end RegularityStructures.Phi43

end
