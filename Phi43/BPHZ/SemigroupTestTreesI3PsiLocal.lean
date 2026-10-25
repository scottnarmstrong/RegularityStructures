/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesCov

/-!
# The local majorant of the covariance of `I₃Ψ` against a semigroup test profile

The local covariance bound of `hairerI3PsiField_cov_bound` (valid for `s(y - x), s(y' - x) ≤ 1`)
is a sum of five terms of the form `s(u - x)^ζ s(u - v)^e` or `s(v - x)^ζ s(u - v)^e`; each has a
double bound against a semigroup test profile, and `i3PsiLocalMajorant` is their sum, with total
bound `i3PsiLocalConst * lam^(-δ)`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The local majorant of the covariance of `I₃Ψ`, as a sum of five double-bounded terms. -/
def i3PsiLocalMajorant (x : SpaceTime) (δ : ℝ) (u v : SpaceTime) : ℝ :=
  torusParabolicSize (u - x) ^ (0 : ℝ) * torusParabolicSize (u - v) ^ (-δ) +
    torusParabolicSize (u - x) ^ (-δ) * torusParabolicSize (u - v) ^ (0 : ℝ) +
    torusParabolicSize (v - x) ^ (-δ) * torusParabolicSize (u - v) ^ (0 : ℝ) +
    torusParabolicSize (u - x) ^ (1 - δ) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
    torusParabolicSize (v - x) ^ (1 - δ) * torusParabolicSize (u - v) ^ (-1 : ℝ)

/-- The constant of `SemigroupTestProfile.doubleBound_i3PsiLocal`. -/
def i3PsiLocalConst (B : ℝ) (Mom : ℝ → ℝ) (δ : ℝ) : ℝ :=
  semigroupTestDoubleConst B Mom 0 (-δ) + semigroupTestDoubleConst B Mom (-δ) 0 +
    semigroupTestDoubleConst B Mom (-δ) 0 + semigroupTestDoubleConst B Mom (1 - δ) (-1) +
    semigroupTestDoubleConst B Mom (1 - δ) (-1)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i3PsiLocalMajorant_nonneg (x : SpaceTime) (δ : ℝ) (u v : SpaceTime) :
    0 ≤ i3PsiLocalMajorant x δ u v := by
  unfold i3PsiLocalMajorant
  have h : ∀ a b : ℝ, 0 ≤ torusParabolicSize (u - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have h' : ∀ a b : ℝ, 0 ≤ torusParabolicSize (v - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have := h 0 (-δ)
  have := h (-δ) 0
  have := h' (-δ) 0
  have := h (1 - δ) (-1)
  have := h' (1 - δ) (-1)
  linarith

theorem SemigroupTestProfile.doubleBound_i3PsiLocal {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
    {g : SpaceTime → ℝ} (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    SemigroupDoubleBound g (i3PsiLocalMajorant x δ) (i3PsiLocalConst B Mom δ * lam ^ (-δ)) := by
  have t1 := h.doubleBound_fst (ζ := 0) (e := -δ) (by norm_num) (by linarith) hlam
  have t2 := h.doubleBound_fst (ζ := -δ) (e := 0) (by linarith) (by norm_num) hlam
  have t3 := h.doubleBound_snd (ζ := -δ) (e := 0) (by linarith) (by norm_num) hlam
  have t4 := h.doubleBound_fst (ζ := 1 - δ) (e := -1) (by linarith) (by norm_num) hlam
  have t5 := h.doubleBound_snd (ζ := 1 - δ) (e := -1) (by linarith) (by norm_num) hlam
  have s := (((t1.add t2).add t3).add t4).add t5
  refine s.mono_right (le_of_eq ?_)
  unfold i3PsiLocalConst
  rw [show (0 : ℝ) + -δ = -δ by ring, show -δ + 0 = -δ by ring,
    show 1 - δ + -1 = -δ by ring]
  ring

end RegularityStructures

end
