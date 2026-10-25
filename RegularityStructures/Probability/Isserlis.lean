/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianVector

/-!
# The Isserlis–Wick formula for fourth moments

For a centred Gaussian vector `X` with covariance `C`,

* `E[Xᵢ Xⱼ Xₖ Xₗ] = Cᵢⱼ Cₖₗ + Cᵢₖ Cⱼₗ + Cᵢₗ Cⱼₖ` (`integral_mul_mul_mul`);
* `E[(Xᵢ² - Cᵢᵢ)(Xⱼ² - Cⱼⱼ)] = 2 Cᵢⱼ²` (`integral_sq_sub_mul_sq_sub`), the covariance of Wick
  squares;
* `E[Xᵢ Xⱼ Xₖ] = 0` (`IsCentredGaussianVector.integral_mul_mul_eq_zero`, in
  `RegularityStructures.Probability.GaussianVector`).

## Proof

Polarisation. For `x ∈ ℝ⁴`,
`192 x₀ x₁ x₂ x₃ = ∑_{s ∈ {±1}³} s₁ s₂ s₃ (x₀ + s₁ x₁ + s₂ x₂ + s₃ x₃)⁴`.
Each linear form `L = Xᵢ + s₁ Xⱼ + s₂ Xₖ + s₃ Xₗ` is a centred real Gaussian, so
`E[L⁴] = 3 E[L²]²`, and `E[L²]` is a quadratic form in `C`. Summing the eight identities gives the
formula. The same identity, with integrability of each `L⁴`, shows that `Xᵢ Xⱼ Xₖ Xₗ` is integrable.
-/

public section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

/-! ### Polarisation of the fourth power -/

/-- The signs `1, -1`. -/
private def sgn : Fin 2 → ℝ := ![1, -1]

/-- The coefficients `(1, s₁, s₂, s₃)` of the polarising linear forms. -/
private def polCoeff (b : Fin 2 × Fin 2 × Fin 2) : Fin 4 → ℝ :=
  ![1, sgn b.1, sgn b.2.1, sgn b.2.2]

/-- The polarisation weights `s₁ s₂ s₃ / 192`. -/
private noncomputable def polWeight (b : Fin 2 × Fin 2 × Fin 2) : ℝ :=
  sgn b.1 * sgn b.2.1 * sgn b.2.2 / 192

private theorem polarization_four (x : Fin 4 → ℝ) :
    x 0 * x 1 * x 2 * x 3 = ∑ b, polWeight b * (∑ m, polCoeff b m * x m) ^ 4 := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four, polWeight, polCoeff, sgn]
  ring

private theorem mul_mul_mul_eq_sum {Ω : Type*} {n : ℕ} (X : Ω → Fin n → ℝ) (i j k l : Fin n)
    (ω : Ω) :
    X ω i * X ω j * X ω k * X ω l =
      ∑ b, polWeight b * (∑ m, polCoeff b m * X ω (![i, j, k, l] m)) ^ 4 :=
  polarization_four fun m => X ω (![i, j, k, l] m)

namespace IsCentredGaussianVector

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

/-- Products of four coordinates of a Gaussian vector are integrable. -/
theorem integrable_mul_mul_mul (h : IsCentredGaussianVector P X C) (i j k l : Fin n) :
    Integrable (fun ω => X ω i * X ω j * X ω k * X ω l) P := by
  have hsum : Integrable
      (fun ω => ∑ b, polWeight b * (∑ m, polCoeff b m * X ω (![i, j, k, l] m)) ^ 4) P :=
    integrable_finsetSum Finset.univ fun b _ =>
      (h.integrable_linear_pow ![i, j, k, l] (polCoeff b) 4).const_mul (polWeight b)
  exact hsum.congr (ae_of_all _ fun ω => (mul_mul_mul_eq_sum X i j k l ω).symm)

/-- **Isserlis–Wick formula.** For a centred Gaussian vector with covariance `C`,
`E[Xᵢ Xⱼ Xₖ Xₗ] = Cᵢⱼ Cₖₗ + Cᵢₖ Cⱼₗ + Cᵢₗ Cⱼₖ`. -/
theorem integral_mul_mul_mul (h : IsCentredGaussianVector P X C) (i j k l : Fin n) :
    ∫ ω, X ω i * X ω j * X ω k * X ω l ∂P = C i j * C k l + C i k * C j l + C i l * C j k := by
  simp_rw [mul_mul_mul_eq_sum X i j k l]
  rw [integral_finsetSum _ fun b _ =>
    (h.integrable_linear_pow ![i, j, k, l] (polCoeff b) 4).const_mul (polWeight b)]
  simp_rw [integral_const_mul, h.integral_linear_pow_four]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four, polWeight, polCoeff, sgn]
  rw [h.symm j i, h.symm k i, h.symm l i, h.symm k j, h.symm l j, h.symm l k]
  ring

/-- **Covariance of Wick squares.** `E[(Xᵢ² - Cᵢᵢ)(Xⱼ² - Cⱼⱼ)] = 2 Cᵢⱼ²`. -/
theorem integral_sq_sub_mul_sq_sub (h : IsCentredGaussianVector P X C) (i j : Fin n) :
    ∫ ω, (X ω i ^ 2 - C i i) * (X ω j ^ 2 - C j j) ∂P = 2 * C i j ^ 2 := by
  have := h.isProbabilityMeasure
  have hpt : ∀ ω, (X ω i ^ 2 - C i i) * (X ω j ^ 2 - C j j) =
      X ω i * X ω i * X ω j * X ω j - C j j * (X ω i * X ω i) - C i i * (X ω j * X ω j) +
        C i i * C j j := by
    intro ω
    ring
  simp_rw [hpt]
  have i4 := h.integrable_mul_mul_mul i i j j
  have ii := (h.integrable_mul i i).const_mul (C j j)
  have ij := (h.integrable_mul j j).const_mul (C i i)
  have i5 : Integrable (fun ω => X ω i * X ω i * X ω j * X ω j - C j j * (X ω i * X ω i)) P :=
    i4.sub ii
  have i6 : Integrable (fun ω => X ω i * X ω i * X ω j * X ω j - C j j * (X ω i * X ω i) -
      C i i * (X ω j * X ω j)) P := i5.sub ij
  rw [integral_add i6 (integrable_const _), integral_sub i5 ij, integral_sub i4 ii,
    integral_const_mul, integral_const_mul, h.integral_mul_mul_mul, h.integral_mul, h.integral_mul]
  simp
  ring

/-- Products of shifted squares of two coordinates are integrable. -/
theorem integrable_sq_sub_mul_sq_sub (h : IsCentredGaussianVector P X C) (i j : Fin n)
    (a b : ℝ) :
    Integrable (fun ω => (X ω i ^ 2 - a) * (X ω j ^ 2 - b)) P := by
  have := h.isProbabilityMeasure
  have e : (fun ω => (X ω i ^ 2 - a) * (X ω j ^ 2 - b)) =
      fun ω => X ω i ^ 2 * X ω j ^ 2 - b * X ω i ^ 2 - a * X ω j ^ 2 + a * b := by
    funext ω
    ring
  rw [e]
  exact (((h.integrable_pow_mul_pow i j 2 2).sub ((h.integrable_pow_apply i 2).const_mul b)).sub
    ((h.integrable_pow_apply j 2).const_mul a)).add (integrable_const _)

end IsCentredGaussianVector

end RegularityStructures

end
