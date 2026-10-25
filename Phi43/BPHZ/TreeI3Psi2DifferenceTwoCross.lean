/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DifferenceTwoChaos
public import Phi43.BPHZ.TreeI3Psi2FieldCross

/-!
# The tree `I(Ψ³) Ψ²`: cross terms with the counterterm at mixed mollifiers

Generalisation of `integral_integral_mul_hairerPsiWickCube_square_field` to three noises built from
possibly different mollifiers `ρ i` at scales `ε i`:
`E[(∫ g :Ψ³_0:) :Ψ²_1:(y) Ψ_2(y')] = ∫ g(w) 6 Q_{01}(w - y)² Q_{02}(w - y') dw`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The chaos-`1` kernel `6 Q_{01}(w - y)² Q_{02}(w - y')` with mixed mollifiers. -/
def hairerI3Psi2CrossKernelTwo (N : ℕ) (ρ : Fin 3 → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin 3 → ℝ)
    (y y' w : SpaceTime) : ℝ :=
  6 * hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 1) (ε 1) (w - y) ^ 2 *
    hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (w - y')

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : Fin 3 → ℝ × (Fin 3 → ℝ) → ℝ} {ε : Fin 3 → ℝ} {ξ : Fin 3 → Ω → SpaceTime → ℝ}

omit [MeasurableSpace Ω] in
/-- The product `:Ψ³: :Ψ²: Ψ` at three mollifiers is a product of Wick monomials. -/
theorem hairerWickCubeSquareFieldTwo_eq_wickMonomial (N : ℕ) (z : Fin 3 → SpaceTime) (ω : Ω) :
    hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω (z 0) * hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω (z 1) *
        hairerPsiField N (ξ 2) ω (z 2) =
      wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
          (List.replicate 3 0) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
          (List.replicate 2 1) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        hairerPsiField N (ξ 2) ω (z 2) := by
  have c0 := hairerPsiWickCube_eq_wickMonomial_multiscaleTwo N ρ ε ξ z ω 0
  have s1 := hairerPsiWickSquare_eq_wickMonomial_multiscaleTwo N ρ ε ξ z ω 1
  rw [c0, s1]
  rfl

/-- **(W5) for the tree `Ψ`, mixed mollifiers.** -/
theorem hairerPsiWickCubeSquareFieldTwo_integral_mul (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (z : Fin 3 → SpaceTime) :
    ∫ ω, hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω (z 0) *
        hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω (z 1) * hairerPsiField N (ξ 2) ω (z 2) ∂P =
      6 * hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 1) (ε 1) (z 0 - z 1) ^ 2 *
        hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (z 0 - z 2) := by
  have h := hairerPsiField_isCentredGaussianVector_multiscaleTwo N hρ hε hW hξ z
  have hw := integral_wick_three_mul_wick_two_mul_X h 0 1 2
  simp_rw [hairerWickCubeSquareFieldTwo_eq_wickMonomial N z]
  exact hw

/-- The product `:Ψ³: :Ψ²: Ψ` at three mollifiers is integrable. -/
theorem integrable_hairerPsiWickCubeSquareFieldTwo (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (z : Fin 3 → SpaceTime) :
    Integrable (fun ω => hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω (z 0) *
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω (z 1) * hairerPsiField N (ξ 2) ω (z 2)) P := by
  have h := hairerPsiField_isCentredGaussianVector_multiscaleTwo N hρ hε hW hξ z
  have hi := h.integrable_prod_wickMonomial
    (L := ![List.replicate 3 0, List.replicate 2 1, [2]])
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, wickMonomial_singleton] at hi
  exact hi.congr (Filter.Eventually.of_forall fun ω =>
    (hairerWickCubeSquareFieldTwo_eq_wickMonomial N z ω).symm)

private theorem abs_mul_mul_le_young' (a b c : ℝ) :
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

/-- **Uniform first-moment bound** for `:Ψ³_0:(w) :Ψ²_1:(y) Ψ_2(y')` in `w`, mixed mollifiers. -/
theorem exists_integral_abs_hairerPsiWickCubeSquareFieldTwo_le (N : ℕ)
    (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (y y' : SpaceTime) :
    ∃ M : ℝ, ∀ w : SpaceTime,
      ∫ ω, |hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w *
        hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y * hairerPsiField N (ξ 2) ω y'| ∂P ≤ M := by
  have hprob := hW.isProbabilityMeasure
  obtain ⟨A, -, hA⟩ := exists_integral_hairerPsiWickCube_pow_four_le (ρ := ρ 0) (P := P) (W := W)
  refine ⟨((A * (6 * hairerWickConstant N (ρ 0) (ε 0) ^ 3) ^ 2) +
    60 * hairerWickConstant N (ρ 1) (ε 1) ^ 4) / 4 + hairerCovariance N (ρ 2) (ε 2) 0 / 2,
    fun w => ?_⟩
  have i0 := integrable_hairerPsiWickCube_pow_four N (hρ 0) (hε 0) hW (hξ 0) w
  have i1 := integrable_hairerPsiWickSquare_pow_four N (hρ 1) (hε 1) hW (hξ 1) y
  have hL2 := hairerPsiField_memLp N (hρ 2) (hε 2) hW (hξ 2) y'
  have i2 : Integrable (fun ω => hairerPsiField N (ξ 2) ω y' * hairerPsiField N (ξ 2) ω y') P :=
    hL2.integrable_mul hL2
  have j01 : Integrable (fun ω => hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4) P := i0.add i1
  have hz := integrable_hairerPsiWickCubeSquareFieldTwo N hρ hε hW hξ ![w, y, y']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hz
  calc _ ≤ ∫ ω, ((hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 +
          hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4) / 4 +
          (hairerPsiField N (ξ 2) ω y' * hairerPsiField N (ξ 2) ω y') / 2) ∂P :=
        integral_mono hz.abs ((j01.div_const 4).add (i2.div_const 2)) fun ω => by
          have := abs_mul_mul_le_young' (hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w)
            (hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y) (hairerPsiField N (ξ 2) ω y')
          simp only [sq] at this ⊢
          linarith
    _ = (∫ ω, hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 ∂P +
          ∫ ω, hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4 ∂P) / 4 +
          (∫ ω, hairerPsiField N (ξ 2) ω y' * hairerPsiField N (ξ 2) ω y' ∂P) / 2 := by
        rw [integral_add (j01.div_const 4) (i2.div_const 2), integral_div, integral_div,
          integral_add i0 i1]
    _ ≤ _ := by
        rw [integral_hairerPsiWickSquare_pow_four N (hρ 1) (hε 1) hW (hξ 1) y,
          hairerPsiField_integral_mul N (hρ 2) (hε 2) hW (hξ 2) y' y', sub_self]
        have a0 := hA N (hρ 0) (hε 0) hW (hξ 0) w
        linarith

/-- **Fubini for the Wick cube against `:Ψ²:(y) Ψ(y')`**, mixed mollifiers. -/
theorem integral_integral_mul_hairerPsiWickCube_square_fieldTwo (N : ℕ)
    (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) {g : SpaceTime → ℝ} (hg : Integrable g)
    (y y' : SpaceTime) :
    Integrable (fun ω => (∫ w, g w * hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w) *
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y * hairerPsiField N (ξ 2) ω y') P ∧
    ∫ ω, (∫ w, g w * hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w) *
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y * hairerPsiField N (ξ 2) ω y' ∂P =
        ∫ w, g w * hairerI3Psi2CrossKernelTwo N ρ ε y y' w := by
  have hprob := hW.isProbabilityMeasure
  have hYm := measurable_hairerPsiWickCube_uncurry N (hξ 0)
  have hA : Measurable fun ω => hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y :=
    Measurable.comp (g := fun q : Ω × SpaceTime =>
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) q.1 q.2)
      (f := fun ω : Ω => (ω, y)) (measurable_hairerPsiWickSquare_uncurry N (hξ 1))
      (measurable_id.prodMk measurable_const)
  have hB : Measurable fun ω => hairerPsiField N (ξ 2) ω y' :=
    measurable_hairerPsiField_apply N (hξ 2) y'
  obtain ⟨M, hM⟩ := exists_integral_abs_hairerPsiWickCubeSquareFieldTwo_le N hρ hε hW hξ y y'
  have hpt : ∀ ω w, hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w *
      (hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y * hairerPsiField N (ξ 2) ω y') =
      hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w * hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y *
        hairerPsiField N (ξ 2) ω y' := fun ω w => by ring
  obtain ⟨hi, he⟩ := integral_integral_mul_mul_swap_field (P := P) (Y := hairerPsiWickCube N (ρ 0)
    (ε 0) (ξ 0)) (B := fun ω => hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y *
      hairerPsiField N (ξ 2) ω y') hYm (hA.mul hB) hg
    (fun w => by
      have := integrable_hairerPsiWickCubeSquareFieldTwo N hρ hε hW hξ ![w, y, y']
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
  have := hairerPsiWickCubeSquareFieldTwo_integral_mul N hρ hε hW hξ ![w, y, y']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at this
  simp_rw [← mul_assoc]
  rw [this]
  rfl

end RegularityStructures.Phi43

end
