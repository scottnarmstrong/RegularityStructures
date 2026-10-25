/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesCov

/-!
# The local majorant of the covariance of `I(Ψ³)Ψ²` against a semigroup test profile

The local covariance bound of `hairerI3Psi2Field_cov_bound` is `C · i3Psi2Target δ (y - x) (y' - x)`,
a sum of seven terms of the form `s(u - x)^ζ s(u - v)^e` or `s(v - x)^ζ s(u - v)^e` with
`ζ + e ∈ {-(1 + δ), -(1 + 2δ)}`.  For `lam ≤ 1` their sum has the double bound
`i3Psi2LocalConst * lam^(-(1 + 2δ))`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The local majorant of the covariance of `I(Ψ³)Ψ²`. -/
def i3Psi2LocalMajorant (x : SpaceTime) (δ : ℝ) (u v : SpaceTime) : ℝ :=
  torusParabolicSize (u - x) ^ (0 : ℝ) * torusParabolicSize (u - v) ^ (-(1 + δ)) +
    torusParabolicSize (u - x) ^ (1 - δ) * torusParabolicSize (u - v) ^ (-2 : ℝ) +
    torusParabolicSize (v - x) ^ (1 - δ) * torusParabolicSize (u - v) ^ (-2 : ℝ) +
    torusParabolicSize (u - x) ^ (-δ) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
    torusParabolicSize (v - x) ^ (-δ) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
    torusParabolicSize (u - x) ^ (-(1 + 2 * δ)) * torusParabolicSize (u - v) ^ (0 : ℝ) +
    torusParabolicSize (v - x) ^ (-(1 + 2 * δ)) * torusParabolicSize (u - v) ^ (0 : ℝ)

/-- The constant of `SemigroupTestProfile.doubleBound_i3Psi2Local`. -/
def i3Psi2LocalConst (B : ℝ) (Mom : ℝ → ℝ) (δ : ℝ) : ℝ :=
  semigroupTestDoubleConst B Mom 0 (-(1 + δ)) + semigroupTestDoubleConst B Mom (1 - δ) (-2) +
    semigroupTestDoubleConst B Mom (1 - δ) (-2) + semigroupTestDoubleConst B Mom (-δ) (-1) +
    semigroupTestDoubleConst B Mom (-δ) (-1) + semigroupTestDoubleConst B Mom (-(1 + 2 * δ)) 0 +
    semigroupTestDoubleConst B Mom (-(1 + 2 * δ)) 0

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i3Psi2LocalMajorant_nonneg (x : SpaceTime) (δ : ℝ) (u v : SpaceTime) :
    0 ≤ i3Psi2LocalMajorant x δ u v := by
  unfold i3Psi2LocalMajorant
  have h : ∀ a b : ℝ, 0 ≤ torusParabolicSize (u - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have h' : ∀ a b : ℝ, 0 ≤ torusParabolicSize (v - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have := h 0 (-(1 + δ))
  have := h (1 - δ) (-2)
  have := h' (1 - δ) (-2)
  have := h (-δ) (-1)
  have := h' (-δ) (-1)
  have := h (-(1 + 2 * δ)) 0
  have := h' (-(1 + 2 * δ)) 0
  linarith

theorem SemigroupTestProfile.doubleBound_i3Psi2Local {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
    {g : SpaceTime → ℝ} (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    SemigroupDoubleBound g (i3Psi2LocalMajorant x δ)
      (i3Psi2LocalConst B Mom δ * lam ^ (-(1 + 2 * δ))) := by
  have t1 := h.doubleBound_fst (ζ := 0) (e := -(1 + δ)) (by norm_num) (by linarith) hlam
  have t2 := h.doubleBound_fst (ζ := 1 - δ) (e := -2) (by linarith) (by norm_num) hlam
  have t3 := h.doubleBound_snd (ζ := 1 - δ) (e := -2) (by linarith) (by norm_num) hlam
  have t4 := h.doubleBound_fst (ζ := -δ) (e := -1) (by linarith) (by norm_num) hlam
  have t5 := h.doubleBound_snd (ζ := -δ) (e := -1) (by linarith) (by norm_num) hlam
  have t6 := h.doubleBound_fst (ζ := -(1 + 2 * δ)) (e := 0) (by linarith) (by norm_num) hlam
  have t7 := h.doubleBound_snd (ζ := -(1 + 2 * δ)) (e := 0) (by linarith) (by norm_num) hlam
  have c1 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 0) (e := -(1 + δ)) (by norm_num)
    (by linarith) (by linarith)
  have c2 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 1 - δ) (e := -2) (by linarith)
    (by norm_num) (by linarith)
  have c4 := h.semigroupTestDoubleConst_nonneg hlam (ζ := -δ) (e := -1) (by linarith)
    (by norm_num) (by linarith)
  have c6 := h.semigroupTestDoubleConst_nonneg hlam (ζ := -(1 + 2 * δ)) (e := 0) (by linarith)
    (by norm_num) (by linarith)
  have l1 : lam ^ (0 + -(1 + δ)) ≤ lam ^ (-(1 + 2 * δ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l2 : lam ^ (1 - δ + -2) ≤ lam ^ (-(1 + 2 * δ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l4 : lam ^ (-δ + -1) ≤ lam ^ (-(1 + 2 * δ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l6 : lam ^ (-(1 + 2 * δ) + 0) ≤ lam ^ (-(1 + 2 * δ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have s := ((((((t1.add t2).add t3).add t4).add t5).add t6).add t7)
  refine s.mono_right ?_
  unfold i3Psi2LocalConst
  have m1 := mul_le_mul_of_nonneg_left l1 c1
  have m2 := mul_le_mul_of_nonneg_left l2 c2
  have m4 := mul_le_mul_of_nonneg_left l4 c4
  have m6 := mul_le_mul_of_nonneg_left l6 c6
  linarith [m1, m2, m4, m6]

end RegularityStructures

end
