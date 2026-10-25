/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesCov

/-!
# The local majorant of the covariance of `I(Ψ²) Ψ²` against a semigroup test profile

The local covariance bound of `hairerI2Psi2Field_cov_bound` (valid for `s(y - x), s(y' - x) ≤ 1`)
is dominated by a sum of seven terms of the form `s(u - x)^ζ s(u - v)^e` or
`s(v - x)^ζ s(u - v)^e` (the product `r^a r'^a` is bounded by `r^(2a) + r'^(2a)`); each has a
double bound against a semigroup test profile, and for `lam ≤ 1` and `δ ∈ (0, 1/2]` their sum has the
bound `i2Psi2LocalConst * lam^(-δ)` with `δ₁ = δ/2`, `a = (1 - δ)/2`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The local majorant of the covariance of `I(Ψ²) Ψ²`, as a sum of seven double-bounded terms. -/
def i2Psi2LocalMajorant (x : SpaceTime) (δ₁ a : ℝ) (u v : SpaceTime) : ℝ :=
  torusParabolicSize (u - x) ^ (0 : ℝ) * torusParabolicSize (u - v) ^ (-δ₁) +
    torusParabolicSize (u - x) ^ (2 - δ₁) * torusParabolicSize (u - v) ^ (-2 : ℝ) +
    torusParabolicSize (v - x) ^ (2 - δ₁) * torusParabolicSize (u - v) ^ (-2 : ℝ) +
    torusParabolicSize (u - x) ^ (2 * a) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
    torusParabolicSize (v - x) ^ (2 * a) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
    torusParabolicSize (u - x) ^ (-(2 * δ₁)) * torusParabolicSize (u - v) ^ (0 : ℝ) +
    torusParabolicSize (v - x) ^ (-(2 * δ₁)) * torusParabolicSize (u - v) ^ (0 : ℝ)

/-- The constant of `SemigroupTestProfile.doubleBound_i2Psi2Local`. -/
def i2Psi2LocalConst (B : ℝ) (Mom : ℝ → ℝ) (δ₁ a : ℝ) : ℝ :=
  semigroupTestDoubleConst B Mom 0 (-δ₁) + semigroupTestDoubleConst B Mom (2 - δ₁) (-2) +
    semigroupTestDoubleConst B Mom (2 - δ₁) (-2) + semigroupTestDoubleConst B Mom (2 * a) (-1) +
    semigroupTestDoubleConst B Mom (2 * a) (-1) + semigroupTestDoubleConst B Mom (-(2 * δ₁)) 0 +
    semigroupTestDoubleConst B Mom (-(2 * δ₁)) 0

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i2Psi2LocalMajorant_nonneg (x : SpaceTime) (δ₁ a : ℝ) (u v : SpaceTime) :
    0 ≤ i2Psi2LocalMajorant x δ₁ a u v := by
  unfold i2Psi2LocalMajorant
  have h : ∀ a b : ℝ, 0 ≤ torusParabolicSize (u - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have h' : ∀ a b : ℝ, 0 ≤ torusParabolicSize (v - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have := h 0 (-δ₁)
  have := h (2 - δ₁) (-2)
  have := h' (2 - δ₁) (-2)
  have := h (2 * a) (-1)
  have := h' (2 * a) (-1)
  have := h (-(2 * δ₁)) 0
  have := h' (-(2 * δ₁)) 0
  linarith

theorem SemigroupTestProfile.doubleBound_i2Psi2Local {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
    {g : SpaceTime → ℝ} (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    SemigroupDoubleBound g (i2Psi2LocalMajorant x (δ / 2) ((1 - δ) / 2))
      (i2Psi2LocalConst B Mom (δ / 2) ((1 - δ) / 2) * lam ^ (-δ)) := by
  have t1 := h.doubleBound_fst (ζ := 0) (e := -(δ / 2)) (by norm_num) (by linarith) hlam
  have t2 := h.doubleBound_fst (ζ := 2 - δ / 2) (e := -2) (by linarith) (by norm_num) hlam
  have t3 := h.doubleBound_snd (ζ := 2 - δ / 2) (e := -2) (by linarith) (by norm_num) hlam
  have t4 := h.doubleBound_fst (ζ := 2 * ((1 - δ) / 2)) (e := -1) (by linarith) (by norm_num) hlam
  have t5 := h.doubleBound_snd (ζ := 2 * ((1 - δ) / 2)) (e := -1) (by linarith) (by norm_num) hlam
  have t6 := h.doubleBound_fst (ζ := -(2 * (δ / 2))) (e := 0) (by linarith) (by norm_num) hlam
  have t7 := h.doubleBound_snd (ζ := -(2 * (δ / 2))) (e := 0) (by linarith) (by norm_num) hlam
  have c1 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 0) (e := -(δ / 2)) (by norm_num)
    (by linarith) (by linarith)
  have c2 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 2 - δ / 2) (e := -2) (by linarith)
    (by norm_num) (by linarith)
  have c4 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 2 * ((1 - δ) / 2)) (e := -1)
    (by linarith) (by norm_num) (by linarith)
  have c6 := h.semigroupTestDoubleConst_nonneg hlam (ζ := -(2 * (δ / 2))) (e := 0) (by linarith)
    (by norm_num) (by linarith)
  have l1 : lam ^ (0 + -(δ / 2)) ≤ lam ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l2 : lam ^ (2 - δ / 2 + -2) ≤ lam ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l4 : lam ^ (2 * ((1 - δ) / 2) + -1) ≤ lam ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l6 : lam ^ (-(2 * (δ / 2)) + 0) ≤ lam ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have s := ((((((t1.add t2).add t3).add t4).add t5).add t6).add t7)
  refine s.mono_right ?_
  unfold i2Psi2LocalConst
  have m1 := mul_le_mul_of_nonneg_left l1 c1
  have m2 := mul_le_mul_of_nonneg_left l2 c2
  have m4 := mul_le_mul_of_nonneg_left l4 c4
  have m6 := mul_le_mul_of_nonneg_left l6 c6
  linarith [m1, m2, m4, m6]

end RegularityStructures

end
