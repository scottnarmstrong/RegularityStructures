/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesCov
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiTarget

/-!
# The local majorant of the covariance of the difference of `I(Ψ³)Ψ²` against a semigroup test

The local covariance bound of `hairerI3Psi2Field_sub_cov_bound_cross` is
`C (max ε ε')^(2θ) i3Psi2DiffTarget δ θ (y - x) (y' - x)`, a sum of eleven terms of the form
`s(u - x)^ζ s(u - v)^e` or `s(v - x)^ζ s(u - v)^e` with `ζ + e ≥ -(1 + 2δ + 2θ)`.  For `lam ≤ 1`
their sum has the double bound `i3Psi2DiffLocalConst * lam^(-(1 + 2δ + 2θ))`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The local majorant of the covariance of the difference of `I(Ψ³)Ψ²`. -/
def i3Psi2DiffLocalMajorant (x : SpaceTime) (δ θ : ℝ) (u v : SpaceTime) : ℝ :=
  torusParabolicSize (u - x) ^ (0 : ℝ) * torusParabolicSize (u - v) ^ (-(1 + δ + 2 * θ)) +
    torusParabolicSize (u - x) ^ (1 - δ - 2 * θ) * torusParabolicSize (u - v) ^ (-2 : ℝ) +
    torusParabolicSize (v - x) ^ (1 - δ - 2 * θ) * torusParabolicSize (u - v) ^ (-2 : ℝ) +
    torusParabolicSize (u - x) ^ (1 - δ) * torusParabolicSize (u - v) ^ (-(2 + 2 * θ)) +
    torusParabolicSize (v - x) ^ (1 - δ) * torusParabolicSize (u - v) ^ (-(2 + 2 * θ)) +
    torusParabolicSize (u - x) ^ (-(δ + 2 * θ)) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
    torusParabolicSize (v - x) ^ (-(δ + 2 * θ)) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
    torusParabolicSize (u - x) ^ (-δ) * torusParabolicSize (u - v) ^ (-(1 + 2 * θ)) +
    torusParabolicSize (v - x) ^ (-δ) * torusParabolicSize (u - v) ^ (-(1 + 2 * θ)) +
    torusParabolicSize (u - x) ^ (-(1 + 2 * δ + 2 * θ)) * torusParabolicSize (u - v) ^ (0 : ℝ) +
    torusParabolicSize (v - x) ^ (-(1 + 2 * δ + 2 * θ)) * torusParabolicSize (u - v) ^ (0 : ℝ)

/-- The constant of `SemigroupTestProfile.doubleBound_i3Psi2DiffLocal`. -/
def i3Psi2DiffLocalConst (B : ℝ) (Mom : ℝ → ℝ) (δ θ : ℝ) : ℝ :=
  semigroupTestDoubleConst B Mom 0 (-(1 + δ + 2 * θ)) +
    semigroupTestDoubleConst B Mom (1 - δ - 2 * θ) (-2) +
    semigroupTestDoubleConst B Mom (1 - δ - 2 * θ) (-2) +
    semigroupTestDoubleConst B Mom (1 - δ) (-(2 + 2 * θ)) +
    semigroupTestDoubleConst B Mom (1 - δ) (-(2 + 2 * θ)) +
    semigroupTestDoubleConst B Mom (-(δ + 2 * θ)) (-1) +
    semigroupTestDoubleConst B Mom (-(δ + 2 * θ)) (-1) +
    semigroupTestDoubleConst B Mom (-δ) (-(1 + 2 * θ)) +
    semigroupTestDoubleConst B Mom (-δ) (-(1 + 2 * θ)) +
    semigroupTestDoubleConst B Mom (-(1 + 2 * δ + 2 * θ)) 0 +
    semigroupTestDoubleConst B Mom (-(1 + 2 * δ + 2 * θ)) 0

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i3Psi2DiffLocalMajorant_eq (x : SpaceTime) (δ θ : ℝ) (u v : SpaceTime) :
    i3Psi2DiffLocalMajorant x δ θ u v = i3Psi2DiffTarget δ θ (u - x) (v - x) := by
  unfold i3Psi2DiffLocalMajorant i3Psi2DiffTarget
  rw [sub_sub_sub_cancel_right]
  simp only [Real.rpow_zero, mul_one, one_mul]
  ring

theorem i3Psi2DiffLocalMajorant_nonneg (x : SpaceTime) (δ θ : ℝ) (u v : SpaceTime) :
    0 ≤ i3Psi2DiffLocalMajorant x δ θ u v := by
  rw [i3Psi2DiffLocalMajorant_eq]
  exact i3Psi2DiffTarget_nonneg δ θ _ _

theorem SemigroupTestProfile.doubleBound_i3Psi2DiffLocal {x : SpaceTime} {lam B : ℝ}
    {Mom : ℝ → ℝ} {g : SpaceTime → ℝ} (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) {δ θ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    SemigroupDoubleBound g (i3Psi2DiffLocalMajorant x δ θ)
      (i3Psi2DiffLocalConst B Mom δ θ * lam ^ (-(1 + 2 * δ + 2 * θ))) := by
  have t1 := h.doubleBound_fst (ζ := 0) (e := -(1 + δ + 2 * θ)) (by norm_num) (by linarith) hlam
  have t2 := h.doubleBound_fst (ζ := 1 - δ - 2 * θ) (e := -2) (by linarith) (by norm_num) hlam
  have t3 := h.doubleBound_snd (ζ := 1 - δ - 2 * θ) (e := -2) (by linarith) (by norm_num) hlam
  have t4 := h.doubleBound_fst (ζ := 1 - δ) (e := -(2 + 2 * θ)) (by linarith) (by linarith) hlam
  have t5 := h.doubleBound_snd (ζ := 1 - δ) (e := -(2 + 2 * θ)) (by linarith) (by linarith) hlam
  have t6 := h.doubleBound_fst (ζ := -(δ + 2 * θ)) (e := -1) (by linarith) (by norm_num) hlam
  have t7 := h.doubleBound_snd (ζ := -(δ + 2 * θ)) (e := -1) (by linarith) (by norm_num) hlam
  have t8 := h.doubleBound_fst (ζ := -δ) (e := -(1 + 2 * θ)) (by linarith) (by linarith) hlam
  have t9 := h.doubleBound_snd (ζ := -δ) (e := -(1 + 2 * θ)) (by linarith) (by linarith) hlam
  have t10 := h.doubleBound_fst (ζ := -(1 + 2 * δ + 2 * θ)) (e := 0) (by linarith) (by norm_num)
    hlam
  have t11 := h.doubleBound_snd (ζ := -(1 + 2 * δ + 2 * θ)) (e := 0) (by linarith) (by norm_num)
    hlam
  have c1 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 0) (e := -(1 + δ + 2 * θ))
    (by norm_num) (by linarith) (by linarith)
  have c2 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 1 - δ - 2 * θ) (e := -2)
    (by linarith) (by norm_num) (by linarith)
  have c4 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 1 - δ) (e := -(2 + 2 * θ))
    (by linarith) (by linarith) (by linarith)
  have c6 := h.semigroupTestDoubleConst_nonneg hlam (ζ := -(δ + 2 * θ)) (e := -1)
    (by linarith) (by norm_num) (by linarith)
  have c8 := h.semigroupTestDoubleConst_nonneg hlam (ζ := -δ) (e := -(1 + 2 * θ))
    (by linarith) (by linarith) (by linarith)
  have c10 := h.semigroupTestDoubleConst_nonneg hlam (ζ := -(1 + 2 * δ + 2 * θ)) (e := 0)
    (by linarith) (by norm_num) (by linarith)
  have l1 : lam ^ (0 + -(1 + δ + 2 * θ)) ≤ lam ^ (-(1 + 2 * δ + 2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l2 : lam ^ (1 - δ - 2 * θ + -2) ≤ lam ^ (-(1 + 2 * δ + 2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l4 : lam ^ (1 - δ + -(2 + 2 * θ)) ≤ lam ^ (-(1 + 2 * δ + 2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l6 : lam ^ (-(δ + 2 * θ) + -1) ≤ lam ^ (-(1 + 2 * δ + 2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l8 : lam ^ (-δ + -(1 + 2 * θ)) ≤ lam ^ (-(1 + 2 * δ + 2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l10 : lam ^ (-(1 + 2 * δ + 2 * θ) + 0) ≤ lam ^ (-(1 + 2 * δ + 2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have s := ((((((((((t1.add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add
    t10).add t11)
  refine s.mono_right ?_
  unfold i3Psi2DiffLocalConst
  have m1 := mul_le_mul_of_nonneg_left l1 c1
  have m2 := mul_le_mul_of_nonneg_left l2 c2
  have m4 := mul_le_mul_of_nonneg_left l4 c4
  have m6 := mul_le_mul_of_nonneg_left l6 c6
  have m8 := mul_le_mul_of_nonneg_left l8 c8
  have m10 := mul_le_mul_of_nonneg_left l10 c10
  linarith [m1, m2, m4, m6, m8, m10]

end RegularityStructures

end
