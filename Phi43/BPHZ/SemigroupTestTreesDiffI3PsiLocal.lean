/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesCov
public import Phi43.BPHZ.SemigroupTestTreesBound

/-!
# The local majorant of the covariance of the cross-mollifier difference of `I₃Ψ`

The local cross covariance bound `hairerI3PsiField_sub_cov_bound_cross` (valid for
`s(y - x), s(y' - x) ≤ 1`) is `C (max ε ε')^(2θ)` times a sum of five terms of the form
`s(u - x)^ζ s(u - v)^e` or `s(v - x)^ζ s(u - v)^e`; each has a double bound against a semigroup
test profile, and `i3PsiDiffLocalMajorant` is their sum, with total bound
`i3PsiDiffLocalConst * lam^(-(2θ + δ))`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The local majorant of the covariance of the cross-mollifier difference of `I₃Ψ`, as a sum of
five double-bounded terms (`η = 2θ + δ`). -/
def i3PsiDiffLocalMajorant (x : SpaceTime) (θ δ : ℝ) (u v : SpaceTime) : ℝ :=
  torusParabolicSize (u - x) ^ (0 : ℝ) * torusParabolicSize (u - v) ^ (-(2 * θ + δ)) +
    torusParabolicSize (u - x) ^ (-(2 * θ + δ)) * torusParabolicSize (u - v) ^ (0 : ℝ) +
    torusParabolicSize (v - x) ^ (-(2 * θ + δ)) * torusParabolicSize (u - v) ^ (0 : ℝ) +
    torusParabolicSize (v - x) ^ (1 - δ - 2 * θ) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
    torusParabolicSize (v - x) ^ (1 - δ) * torusParabolicSize (u - v) ^ (-(1 + 2 * θ))

/-- The constant of `SemigroupTestProfile.doubleBound_i3PsiDiffLocal`. -/
def i3PsiDiffLocalConst (B : ℝ) (Mom : ℝ → ℝ) (θ δ : ℝ) : ℝ :=
  semigroupTestDoubleConst B Mom 0 (-(2 * θ + δ)) +
    semigroupTestDoubleConst B Mom (-(2 * θ + δ)) 0 +
    semigroupTestDoubleConst B Mom (-(2 * θ + δ)) 0 +
    semigroupTestDoubleConst B Mom (1 - δ - 2 * θ) (-1) +
    semigroupTestDoubleConst B Mom (1 - δ) (-(1 + 2 * θ))

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i3PsiDiffLocalMajorant_nonneg (x : SpaceTime) (θ δ : ℝ) (u v : SpaceTime) :
    0 ≤ i3PsiDiffLocalMajorant x θ δ u v := by
  unfold i3PsiDiffLocalMajorant
  have h : ∀ a b : ℝ, 0 ≤ torusParabolicSize (u - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have h' : ∀ a b : ℝ, 0 ≤ torusParabolicSize (v - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have := h 0 (-(2 * θ + δ))
  have := h (-(2 * θ + δ)) 0
  have := h' (-(2 * θ + δ)) 0
  have := h' (1 - δ - 2 * θ) (-1)
  have := h' (1 - δ) (-(1 + 2 * θ))
  linarith

theorem SemigroupTestProfile.doubleBound_i3PsiDiffLocal {x : SpaceTime} {lam B : ℝ}
    {Mom : ℝ → ℝ} {g : SpaceTime → ℝ} (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam)
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ1 : δ ≤ 1 / 4) :
    SemigroupDoubleBound g (i3PsiDiffLocalMajorant x θ δ)
      (i3PsiDiffLocalConst B Mom θ δ * lam ^ (-(2 * θ + δ))) := by
  have t1 := h.doubleBound_fst (ζ := 0) (e := -(2 * θ + δ)) (by norm_num) (by linarith) hlam
  have t2 := h.doubleBound_fst (ζ := -(2 * θ + δ)) (e := 0) (by linarith) (by norm_num) hlam
  have t3 := h.doubleBound_snd (ζ := -(2 * θ + δ)) (e := 0) (by linarith) (by norm_num) hlam
  have t4 := h.doubleBound_snd (ζ := 1 - δ - 2 * θ) (e := -1) (by linarith) (by norm_num) hlam
  have t5 := h.doubleBound_snd (ζ := 1 - δ) (e := -(1 + 2 * θ)) (by linarith) (by linarith) hlam
  have s := (((t1.add t2).add t3).add t4).add t5
  refine s.mono_right (le_of_eq ?_)
  unfold i3PsiDiffLocalConst
  rw [show (0 : ℝ) + -(2 * θ + δ) = -(2 * θ + δ) by ring,
    show -(2 * θ + δ) + 0 = -(2 * θ + δ) by ring,
    show 1 - δ - 2 * θ + -1 = -(2 * θ + δ) by ring,
    show 1 - δ + -(1 + 2 * θ) = -(2 * θ + δ) by ring]
  ring

end RegularityStructures

end
