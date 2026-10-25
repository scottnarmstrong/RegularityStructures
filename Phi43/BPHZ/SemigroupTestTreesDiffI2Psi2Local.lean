/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesCov
public import Phi43.BPHZ.TreeI2Psi2DiagramMultiTriple

/-!
# The local majorant of the cross-difference covariance of `I(Ψ²) Ψ²` against a test profile

The local cross-difference covariance bound (`hairerI2Psi2Field_sub_cov_bound_cross`, valid for
`s(y - x), s(y' - x) ≤ 1`) has the majorant `i2Psi2DiffF θ δ r r' d`, a sum of seven terms of the
form `s(u - x)^ζ s(u - v)^e` or `s(v - x)^ζ s(u - v)^e`, all with `ζ + e = -(2θ + δ)`.  Each has a
double bound against a semigroup test profile, and for `lam ≤ 1` their sum has the bound
`i2Psi2DiffLocalConst * lam^(-(2θ + δ))`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The local majorant `i2Psi2DiffF θ δ s(u - x) s(v - x) s(u - v)` as a sum of seven monomials. -/
def i2Psi2DiffLocalMajorant (x : SpaceTime) (θ δ : ℝ) (u v : SpaceTime) : ℝ :=
  torusParabolicSize (u - x) ^ (0 : ℝ) * torusParabolicSize (u - v) ^ (-(2 * θ + δ)) +
    torusParabolicSize (u - x) ^ (2 - (2 * θ + δ)) * torusParabolicSize (u - v) ^ (-2 : ℝ) +
    torusParabolicSize (v - x) ^ (2 - (2 * θ + δ)) * torusParabolicSize (u - v) ^ (-2 : ℝ) +
    torusParabolicSize (u - x) ^ (2 - δ) * torusParabolicSize (u - v) ^ (-(2 + 2 * θ)) +
    torusParabolicSize (v - x) ^ (2 - δ) * torusParabolicSize (u - v) ^ (-(2 + 2 * θ)) +
    torusParabolicSize (u - x) ^ (-(2 * θ + δ)) * torusParabolicSize (u - v) ^ (0 : ℝ) +
    torusParabolicSize (v - x) ^ (-(2 * θ + δ)) * torusParabolicSize (u - v) ^ (0 : ℝ)

/-- The constant of `SemigroupTestProfile.doubleBound_i2Psi2DiffLocal`. -/
def i2Psi2DiffLocalConst (B : ℝ) (Mom : ℝ → ℝ) (θ δ : ℝ) : ℝ :=
  semigroupTestDoubleConst B Mom 0 (-(2 * θ + δ)) +
    semigroupTestDoubleConst B Mom (2 - (2 * θ + δ)) (-2) +
    semigroupTestDoubleConst B Mom (2 - (2 * θ + δ)) (-2) +
    semigroupTestDoubleConst B Mom (2 - δ) (-(2 + 2 * θ)) +
    semigroupTestDoubleConst B Mom (2 - δ) (-(2 + 2 * θ)) +
    semigroupTestDoubleConst B Mom (-(2 * θ + δ)) 0 +
    semigroupTestDoubleConst B Mom (-(2 * θ + δ)) 0

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i2Psi2DiffLocalMajorant_nonneg (x : SpaceTime) (θ δ : ℝ) (u v : SpaceTime) :
    0 ≤ i2Psi2DiffLocalMajorant x θ δ u v := by
  unfold i2Psi2DiffLocalMajorant
  have h : ∀ a b : ℝ, 0 ≤ torusParabolicSize (u - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have h' : ∀ a b : ℝ, 0 ≤ torusParabolicSize (v - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have := h 0 (-(2 * θ + δ))
  have := h (2 - (2 * θ + δ)) (-2)
  have := h' (2 - (2 * θ + δ)) (-2)
  have := h (2 - δ) (-(2 + 2 * θ))
  have := h' (2 - δ) (-(2 + 2 * θ))
  have := h (-(2 * θ + δ)) 0
  have := h' (-(2 * θ + δ)) 0
  linarith

theorem SemigroupTestProfile.doubleBound_i2Psi2DiffLocal {x : SpaceTime} {lam B : ℝ}
    {Mom : ℝ → ℝ} {g : SpaceTime → ℝ} (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam)
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ1 : δ ≤ 1 / 4) :
    SemigroupDoubleBound g (i2Psi2DiffLocalMajorant x θ δ)
      (i2Psi2DiffLocalConst B Mom θ δ * lam ^ (-(2 * θ + δ))) := by
  have t1 := h.doubleBound_fst (ζ := 0) (e := -(2 * θ + δ)) (by norm_num) (by linarith) hlam
  have t2 := h.doubleBound_fst (ζ := 2 - (2 * θ + δ)) (e := -2) (by linarith) (by norm_num) hlam
  have t3 := h.doubleBound_snd (ζ := 2 - (2 * θ + δ)) (e := -2) (by linarith) (by norm_num) hlam
  have t4 := h.doubleBound_fst (ζ := 2 - δ) (e := -(2 + 2 * θ)) (by linarith) (by linarith) hlam
  have t5 := h.doubleBound_snd (ζ := 2 - δ) (e := -(2 + 2 * θ)) (by linarith) (by linarith) hlam
  have t6 := h.doubleBound_fst (ζ := -(2 * θ + δ)) (e := 0) (by linarith) (by norm_num) hlam
  have t7 := h.doubleBound_snd (ζ := -(2 * θ + δ)) (e := 0) (by linarith) (by norm_num) hlam
  have c1 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 0) (e := -(2 * θ + δ)) (by norm_num)
    (by linarith) (by linarith)
  have c2 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 2 - (2 * θ + δ)) (e := -2)
    (by linarith) (by norm_num) (by linarith)
  have c4 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 2 - δ) (e := -(2 + 2 * θ))
    (by linarith) (by linarith) (by linarith)
  have c6 := h.semigroupTestDoubleConst_nonneg hlam (ζ := -(2 * θ + δ)) (e := 0) (by linarith)
    (by norm_num) (by linarith)
  have l1 : lam ^ (0 + -(2 * θ + δ)) = lam ^ (-(2 * θ + δ)) := by congr 1; ring
  have l2 : lam ^ (2 - (2 * θ + δ) + -2) = lam ^ (-(2 * θ + δ)) := by congr 1; ring
  have l4 : lam ^ (2 - δ + -(2 + 2 * θ)) = lam ^ (-(2 * θ + δ)) := by congr 1; ring
  have l6 : lam ^ (-(2 * θ + δ) + 0) = lam ^ (-(2 * θ + δ)) := by congr 1; ring
  rw [l1] at t1
  rw [l2] at t2 t3
  rw [l4] at t4 t5
  rw [l6] at t6 t7
  have s := ((((((t1.add t2).add t3).add t4).add t5).add t6).add t7)
  refine s.mono_right (le_of_eq ?_)
  unfold i2Psi2DiffLocalConst
  ring

end RegularityStructures

end
