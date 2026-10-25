/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Model.Fubini
public import RegularityStructures.Abstract.Polynomial.Structure

/-!
# Polynomials as `Q`-distributions

The polynomial `z ↦ (z - x)^τ = polyEval x τ z` has polynomial growth, so it is integrable against
`q_t(y - ·)` and `Q_s Q_t (polyEval x τ) = Q_{s+t} (polyEval x τ)`. Its family of regularisations
`polyReg x τ t = Q_t (polyEval x τ)` (and `0` for `t ≤ 0`) is a `Q`-distribution
(`polyReg_mem`), linear in `τ`. This records `Π_x τ` for the polynomial model
[Hai14, Section 2.2, Remark 2.23, (2.20)].
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures

variable {N : ℕ}

/-- The regularisations `t ↦ Q_t (z ↦ (z - x)^τ)` of the polynomial `(· - x)^τ`, extended by `0` to
`t ≤ 0`. -/
noncomputable def polyReg (x : ParabolicSpace) (τ : PolyIndex N → ℝ) :
    ℝ → ParabolicSpace → ℝ := fun t y =>
  if 0 < t then parabolicSemigroup.apply t (polyEval x τ) y else 0

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

variable {N : ℕ}

theorem polyEval_add (x : ParabolicSpace) (τ σ : PolyIndex N → ℝ) :
    polyEval x (τ + σ) = polyEval x τ + polyEval x σ := by
  funext z
  simp [polyEval]

theorem polyEval_smul (x : ParabolicSpace) (c : ℝ) (τ : PolyIndex N → ℝ) :
    polyEval x (c • τ) = c • polyEval x τ := by
  funext z
  simp [polyEval]

theorem polyEval_eq_sum (x : ParabolicSpace) (τ : PolyIndex N → ℝ) (z : ParabolicSpace) :
    polyEval x τ z = ∑ k, τ k * evalParabolic (MvPolynomial.monomial k.1 1) (z - x) := by
  simp [polyEval, toPoly_apply, evalParabolic, MvPolynomial.smul_eval]

theorem continuous_polyEval (x : ParabolicSpace) (τ : PolyIndex N → ℝ) :
    Continuous (polyEval x τ) := by
  have : polyEval x τ = fun z => ∑ k, τ k * evalParabolic (MvPolynomial.monomial k.1 1) (z - x) :=
    funext (polyEval_eq_sum x τ)
  rw [this]
  exact continuous_finsetSum _ fun k _ =>
    continuous_const.mul ((continuous_evalParabolic _).comp (continuous_id.sub continuous_const))

theorem measurable_polyEval (x : ParabolicSpace) (τ : PolyIndex N → ℝ) :
    Measurable (polyEval x τ) :=
  (continuous_polyEval x τ).measurable

/-- `|polyEval x τ z| ≤ (∑ₖ |τ_k|) (1 + ‖x‖_𝔰)^N (1 + ‖z‖_𝔰)^N`. -/
theorem abs_polyEval_le (x : ParabolicSpace) (τ : PolyIndex N → ℝ) (z : ParabolicSpace) :
    |polyEval x τ z| ≤ (∑ k, |τ k|) * (1 + parabolicNorm x) ^ N * (1 + parabolicNorm z) ^ N := by
  have hz := parabolicNorm_nonneg z
  have hx := parabolicNorm_nonneg x
  have hzx := parabolicNorm_nonneg (z - x)
  have h1 : 1 + parabolicNorm (z - x) ≤ (1 + parabolicNorm x) * (1 + parabolicNorm z) := by
    have h := parabolicNorm_add_le z (-x)
    rw [parabolicNorm_neg, ← sub_eq_add_neg] at h
    have := mul_nonneg hx hz
    linarith [mul_add (1 + parabolicNorm x) 1 (parabolicNorm z)]
  have h2 : ∀ k : PolyIndex N, |evalParabolic (MvPolynomial.monomial k.1 1) (z - x)| ≤
      ((1 + parabolicNorm x) * (1 + parabolicNorm z)) ^ N := by
    intro k
    refine (abs_evalParabolic_monomial_le _ _).trans ?_
    have hk := k.2
    rw [weight_parabolicWeight] at hk
    calc parabolicNorm (z - x) ^ (2 * k.1 0 + k.1 1 + k.1 2 + k.1 3)
        ≤ (1 + parabolicNorm (z - x)) ^ (2 * k.1 0 + k.1 1 + k.1 2 + k.1 3) :=
          pow_le_pow_left₀ hzx (by linarith) _
      _ ≤ (1 + parabolicNorm (z - x)) ^ N :=
          pow_le_pow_right₀ (by linarith) hk.le
      _ ≤ _ := pow_le_pow_left₀ (by linarith) h1 N
  rw [polyEval_eq_sum]
  calc |∑ k, τ k * evalParabolic (MvPolynomial.monomial k.1 1) (z - x)|
      ≤ ∑ k, |τ k * evalParabolic (MvPolynomial.monomial k.1 1) (z - x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |τ k| * ((1 + parabolicNorm x) * (1 + parabolicNorm z)) ^ N := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (h2 k) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_pow]; ring

theorem polyBounded_polyEval (x : ParabolicSpace) (τ : PolyIndex N → ℝ) :
    PolyBounded (polyEval x τ) :=
  ⟨measurable_polyEval x τ, _, N, abs_polyEval_le x τ⟩

/-- Target 1: `z ↦ q_t(y - z) (z - x)^τ` is integrable. -/
theorem integrable_parabolicKernel_mul_polyEval (x : ParabolicSpace) (τ : PolyIndex N → ℝ)
    {t : ℝ} (ht : 0 < t) (y : ParabolicSpace) :
    Integrable (fun z => parabolicKernel t (y - z) * polyEval x τ z) :=
  (polyBounded_polyEval x τ).integrable_parabolicKernel_mul ht y

/-- Target 1: the semigroup property for polynomials. -/
theorem apply_apply_polyEval (x : ParabolicSpace) (τ : PolyIndex N → ℝ) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (y : ParabolicSpace) :
    parabolicSemigroup.apply s (parabolicSemigroup.apply t (polyEval x τ)) y =
      parabolicSemigroup.apply (s + t) (polyEval x τ) y :=
  (polyBounded_polyEval x τ).apply_apply hs ht y

theorem polyReg_of_pos (x : ParabolicSpace) (τ : PolyIndex N → ℝ) {t : ℝ} (ht : 0 < t) :
    polyReg x τ t = parabolicSemigroup.apply t (polyEval x τ) := by
  funext y
  simp [polyReg, ht]

theorem polyReg_of_nonpos (x : ParabolicSpace) (τ : PolyIndex N → ℝ) {t : ℝ} (ht : t ≤ 0) :
    polyReg x τ t = 0 := by
  funext y
  simp [polyReg, not_lt.2 ht]

/-- Target 2: `polyReg x τ` is a `Q`-distribution. -/
theorem polyReg_mem (x : ParabolicSpace) (τ : PolyIndex N → ℝ) :
    polyReg x τ ∈ parabolicSemigroup.distributions := by
  refine ⟨fun t ht => polyReg_of_nonpos x τ ht, fun s t hs ht y => ?_⟩
  rw [polyReg_of_pos x τ ht, polyReg_of_pos x τ (add_pos hs ht)]
  exact ⟨((polyBounded_polyEval x τ).apply ht).integrable_parabolicKernel_mul hs y,
    apply_apply_polyEval x τ hs ht y⟩

theorem polyReg_add (x : ParabolicSpace) (τ σ : PolyIndex N → ℝ) :
    polyReg x (τ + σ) = polyReg x τ + polyReg x σ := by
  funext t y
  by_cases ht : 0 < t
  · simp only [polyReg, ht, ite_true, Pi.add_apply, RegularisingSemigroup.apply]
    rw [polyEval_add]
    simp only [Pi.add_apply, mul_add]
    exact integral_add (integrable_parabolicKernel_mul_polyEval x τ ht y)
      (integrable_parabolicKernel_mul_polyEval x σ ht y)
  · simp [polyReg, ht]

theorem polyReg_smul (x : ParabolicSpace) (c : ℝ) (τ : PolyIndex N → ℝ) :
    polyReg x (c • τ) = c • polyReg x τ := by
  funext t y
  by_cases ht : 0 < t
  · simp only [polyReg, ht, ite_true, Pi.smul_apply, smul_eq_mul, RegularisingSemigroup.apply]
    rw [polyEval_smul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
    exact integral_const_mul _ _
  · simp [polyReg, ht]

/-- Target 2: `τ ↦ Π_x τ` as a linear map into the `Q`-distributions. -/
@[expose] noncomputable def polyRegLin (N : ℕ) (x : ParabolicSpace) :
    (PolyIndex N → ℝ) →ₗ[ℝ] parabolicSemigroup.distributions where
  toFun τ := ⟨polyReg x τ, polyReg_mem x τ⟩
  map_add' τ σ := Subtype.ext (polyReg_add x τ σ)
  map_smul' c τ := Subtype.ext (polyReg_smul x c τ)

theorem polyRegLin_apply (x : ParabolicSpace) (τ : PolyIndex N → ℝ) :
    ((polyRegLin N x τ : parabolicSemigroup.distributions) : ℝ → ParabolicSpace → ℝ) =
      polyReg x τ := rfl

end RegularityStructures

end
