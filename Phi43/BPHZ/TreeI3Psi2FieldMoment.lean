/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2FieldWick
public import RegularityStructures.BPHZ.WhiteNoiseChaosMomentsLinear
public import Phi43.BPHZ.TreeWickSquare

/-!
# The tree `I(Ψ³) Ψ²`: moment bounds for the four-fold product

The Wick cube `:Ψ³:(z)` is a cubic polynomial of the Gaussian variable `Ψ(z)`, so by moment
equivalence for Gaussian polynomials `E[:Ψ³:(z)⁴] ≤ A (E[:Ψ³:(z)²])² = 36 A c_ε⁶`
(`exists_integral_hairerPsiWickCube_pow_four_le`). Together with `E[:Ψ²:(z)⁴] = 60 c_ε⁴` this bounds
`E|:Ψ³:(w) :Ψ²:(y) :Ψ³:(w') :Ψ²:(y')|` uniformly in `(w, w')`
(`exists_integral_abs_hairerWickCubeSquareFourProduct_le`), which is the input of the double Fubini
step.
-/

public section

open MeasureTheory MvPolynomial

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The Wick cube is a polynomial of degree `3` in the Gaussian variable `Ψ(z)`. -/
private theorem hairerPsiWickCube_eq_eval (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (ω : Ω) (z : SpaceTime) :
    hairerPsiWickCube N ρ ε ξ ω z =
      eval (fun _ : Fin 1 => hairerPsiField N ξ ω z)
        ((X 0 : MvPolynomial (Fin 1) ℝ) ^ 3 - C (3 * hairerWickConstant N ρ ε) * X 0) := by
  simp [hairerPsiWickCube]

private theorem totalDegree_wickCubePoly (c : ℝ) :
    ((X 0 : MvPolynomial (Fin 1) ℝ) ^ 3 - C (3 * c) * X 0).totalDegree ≤ 3 := by
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_pow _ _).trans ?_
    have := totalDegree_X (R := ℝ) (0 : Fin 1)
    omega
  · refine (totalDegree_mul _ _).trans ?_
    have := totalDegree_X (R := ℝ) (0 : Fin 1)
    rw [totalDegree_C]
    omega

/-- **Fourth moment of the Wick cube.** There is an absolute constant `A ≥ 0` with
`E[:Ψ³:(z)⁴] ≤ A (6 c_ε³)²`. -/
theorem exists_integral_hairerPsiWickCube_pow_four_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ), IsMollifier ρ → ∀ {ε : ℝ}, 0 < ε → IsWhiteNoise P W →
      ∀ {ξ : Ω → SpaceTime → ℝ}, IsRegularisedNoise P W ρ ε ξ → ∀ (z : SpaceTime),
      ∫ ω, hairerPsiWickCube N ρ ε ξ ω z ^ 4 ∂P ≤ A * (6 * hairerWickConstant N ρ ε ^ 3) ^ 2 := by
  obtain ⟨A, hA0, hA⟩ := exists_integral_eval_pow_two_mul_le_of_isCentredGaussianVector.{u}
    3 2 (by norm_num)
  refine ⟨A, hA0, fun N hρ ε hε hW ξ hξ z => ?_⟩
  have h := hairerPsiField_isCentredGaussianVector N hρ hε hW hξ (fun _ : Fin 1 => z)
  have h2 := hA h _ (totalDegree_wickCubePoly (hairerWickConstant N ρ ε))
  have e : ∀ ω, hairerPsiWickCube N ρ ε ξ ω z =
      eval (fun _ : Fin 1 => hairerPsiField N ξ ω z)
        ((X 0 : MvPolynomial (Fin 1) ℝ) ^ 3 - C (3 * hairerWickConstant N ρ ε) * X 0) :=
    fun ω => hairerPsiWickCube_eq_eval N ρ ε ξ ω z
  have hv : ∫ ω, hairerPsiWickCube N ρ ε ξ ω z ^ 2 ∂P = 6 * hairerWickConstant N ρ ε ^ 3 := by
    have := hairerPsiWickCube_integral_mul N hρ hε hW hξ z z
    simp only [sub_self, ← hairerWickConstant_eq_covariance_zero] at this
    simpa only [sq] using this
  simp only [← e] at h2
  rw [hv] at h2
  exact h2

private theorem abs_mul_four_le' (a b c d : ℝ) :
    |a * b * c * d| ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  have h1 : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have h2 : |c * d| ≤ (c ^ 2 + d ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|c| - |d|), sq_abs c, sq_abs d]
  have h3 : |a * b * c * d| ≤ (a ^ 2 + b ^ 2) / 2 * ((c ^ 2 + d ^ 2) / 2) := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  nlinarith [sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - d ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
    sq_nonneg (b ^ 2 - d ^ 2)]

variable {ε : Fin 4 → ℝ} {ξ : Fin 4 → Ω → SpaceTime → ℝ}

/-- The fourth power of the Wick cube is integrable. -/
theorem integrable_hairerPsiWickCube_pow_four (N : ℕ) (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : 0 < ε) (hW : IsWhiteNoise P W) {ξ : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    Integrable (fun ω => hairerPsiWickCube N ρ ε ξ ω z ^ 4) P := by
  have h := hairerPsiField_isCentredGaussianVector_multiscale N hρ (ε := fun _ : Fin 1 => ε)
    (ξ := fun _ => ξ) (fun _ => hε) hW (fun _ => hξ) (fun _ => z)
  have hi := h.integrable_prod_wickMonomial (L := fun _ : Fin 4 => [0, 0, 0])
  refine hi.congr (Filter.Eventually.of_forall fun ω => ?_)
  have e : hairerPsiWickCube N ρ ε ξ ω z =
      wickMonomial (fun a b => hairerCrossCovariance N ρ ε ε (z - z)) [0, 0, 0]
        (fun j : Fin 1 => hairerPsiField N ξ ω z) :=
    hairerPsiWickCube_eq_wickMonomial_multiscale (ρ := ρ) N (fun _ : Fin 1 => ε) (fun _ => ξ)
      (fun _ => z) ω 0
  beta_reduce
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, e]

/-- **Uniform first-moment bound for the four-fold product.** There is `M` with
`E|:Ψ³_{ε₀}:(w) :Ψ²_{ε₁}:(y) :Ψ³_{ε₂}:(w') :Ψ²_{ε₃}:(y')| ≤ M` for all `y, y', w, w'`. -/
theorem exists_integral_abs_hairerWickCubeSquareFourProduct_le (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) :
    ∃ M : ℝ, ∀ y y' w w' : SpaceTime,
      ∫ ω, |hairerWickCubeSquareFourProduct N ρ ε ξ y y' w w' ω| ∂P ≤ M := by
  have hprob := hW.isProbabilityMeasure
  obtain ⟨A, -, hA⟩ := exists_integral_hairerPsiWickCube_pow_four_le (ρ := ρ) (P := P) (W := W)
  refine ⟨(A * (6 * hairerWickConstant N ρ (ε 0) ^ 3) ^ 2 +
    60 * hairerWickConstant N ρ (ε 1) ^ 4 +
    A * (6 * hairerWickConstant N ρ (ε 2) ^ 3) ^ 2 +
    60 * hairerWickConstant N ρ (ε 3) ^ 4) / 4, fun y y' w w' => ?_⟩
  have i0 := integrable_hairerPsiWickCube_pow_four N hρ (hε 0) hW (hξ 0) w
  have i1 := integrable_hairerPsiWickSquare_pow_four N hρ (hε 1) hW (hξ 1) y
  have i2 := integrable_hairerPsiWickCube_pow_four N hρ (hε 2) hW (hξ 2) w'
  have i3 := integrable_hairerPsiWickSquare_pow_four N hρ (hε 3) hW (hξ 3) y'
  have j01 : Integrable (fun ω => hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4) P := i0.add i1
  have j012 : Integrable (fun ω => hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4 +
      hairerPsiWickCube N ρ (ε 2) (ξ 2) ω w' ^ 4) P := j01.add i2
  have j0123 : Integrable (fun ω => hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4 +
      hairerPsiWickCube N ρ (ε 2) (ξ 2) ω w' ^ 4 +
      hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω y' ^ 4) P := j012.add i3
  calc _ ≤ ∫ ω, (hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w ^ 4 +
        hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4 + hairerPsiWickCube N ρ (ε 2) (ξ 2) ω w' ^ 4 +
        hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω y' ^ 4) / 4 ∂P :=
        integral_mono (integrable_hairerWickCubeSquareFourProduct N hρ hε hW hξ y y' w w').abs
          (j0123.div_const 4) fun ω => abs_mul_four_le' _ _ _ _
    _ = (∫ ω, hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w ^ 4 ∂P +
        ∫ ω, hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4 ∂P +
        ∫ ω, hairerPsiWickCube N ρ (ε 2) (ξ 2) ω w' ^ 4 ∂P +
        ∫ ω, hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω y' ^ 4 ∂P) / 4 := by
        rw [integral_div, integral_add j012 i3, integral_add j01 i2, integral_add i0 i1]
    _ ≤ _ := by
        rw [integral_hairerPsiWickSquare_pow_four N hρ (hε 1) hW (hξ 1) y,
          integral_hairerPsiWickSquare_pow_four N hρ (hε 3) hW (hξ 3) y']
        have a0 := hA N hρ (hε 0) hW (hξ 0) w
        have a2 := hA N hρ (hε 2) hW (hξ 2) w'
        linarith

end RegularityStructures.Phi43

end
