/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI2Psi2Single
public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Alg

/-!
# Elementary inequalities for the global difference bound of `I(Ψ²) Ψ²`

`i2Psi2DiffSg θ x y y' = s(y - y')^(-(2+2θ)) + s(x - y)^(-1) + s(x - y')^(-1) + 1` is the singular
factor of the global bound.  Squares of centred powers of exponent `z ≤ 1/2` are dominated by it
(`i2Psi2Diff_sq_pieces`), and a product `(u + v)(u' + v')` by the sum of the four squares.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The singular factor of the global cross-difference bound. -/
def i2Psi2DiffSg (θ : ℝ) (x y y' : SpaceTime) : ℝ :=
  torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) + torusParabolicSize (x - y) ^ (-(1 : ℝ)) +
    torusParabolicSize (x - y') ^ (-(1 : ℝ)) + 1

end RegularityStructures

end

public section

namespace RegularityStructures

/-- `s^(-e) ≤ s^(-f) + 1` for `0 ≤ e ≤ f`. -/
theorem i2Psi2Diff_rpow_neg_le {s e f : ℝ} (hs : 0 < s) (he : 0 ≤ e) (hef : e ≤ f) :
    s ^ (-e) ≤ s ^ (-f) + 1 := by
  rcases le_total s 1 with h | h
  · have : s ^ (-e) ≤ s ^ (-f) := Real.rpow_le_rpow_of_exponent_ge hs h (by linarith)
    have := Real.rpow_nonneg hs.le (-f)
    linarith
  · have : s ^ (-e) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    have := Real.rpow_nonneg hs.le (-f)
    linarith

theorem rpow_neg_sq_eq {s : ℝ} (hs : 0 ≤ s) (z : ℝ) : (s ^ (-z)) ^ 2 = s ^ (-(2 * z)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
  norm_num
  ring_nf

theorem i2Psi2DiffSg_nonneg (θ : ℝ) (x y y' : SpaceTime) : 0 ≤ i2Psi2DiffSg θ x y y' := by
  unfold i2Psi2DiffSg
  have nn : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have := nn (y - y') (-(2 + 2 * θ))
  have := nn (x - y) (-(1 : ℝ))
  have := nn (x - y') (-(1 : ℝ))
  linarith

/-- Squares of centred powers with exponent `z ∈ [0, 1/2]` are dominated by the singular factor. -/
theorem i2Psi2Diff_sq_pieces {θ z : ℝ} (hθ : 0 ≤ θ) (hz0 : 0 ≤ z) (hz : 2 * z ≤ 1)
    {x y y' : SpaceTime} (hyy : 0 < torusParabolicSize (y - y'))
    (hxy : 0 < torusParabolicSize (x - y)) (hxy' : 0 < torusParabolicSize (x - y')) :
    (torusParabolicSize (y - y') ^ (-z)) ^ 2 ≤ i2Psi2DiffSg θ x y y' ∧
    (torusParabolicSize (y' - y) ^ (-z)) ^ 2 ≤ 2 * i2Psi2DiffSg θ x y y' ∧
    (torusParabolicSize (x - y) ^ (-z)) ^ 2 ≤ i2Psi2DiffSg θ x y y' ∧
    (torusParabolicSize (x - y') ^ (-z)) ^ 2 ≤ i2Psi2DiffSg θ x y y' := by
  have nn : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n1 := nn (y - y') (-(2 + 2 * θ))
  have n2 := nn (x - y) (-(1 : ℝ))
  have n3 := nn (x - y') (-(1 : ℝ))
  have k1 : torusParabolicSize (y - y') ^ (-(2 * z)) ≤
      torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) + 1 :=
    i2Psi2Diff_rpow_neg_le hyy (by linarith) (by linarith)
  have k2 : torusParabolicSize (x - y) ^ (-(2 * z)) ≤ torusParabolicSize (x - y) ^ (-(1 : ℝ)) + 1 :=
    i2Psi2Diff_rpow_neg_le hxy (by linarith) (by linarith)
  have k3 : torusParabolicSize (x - y') ^ (-(2 * z)) ≤
      torusParabolicSize (x - y') ^ (-(1 : ℝ)) + 1 :=
    i2Psi2Diff_rpow_neg_le hxy' (by linarith) (by linarith)
  have k4 : torusParabolicSize (y' - y) ^ (-(2 * z)) ≤ 2 * torusParabolicSize (y - y') ^ (-(2 * z)) :=
    torusParabolicSize_sub_rpow_neg_le (a := y') (b := y) (by linarith) hz hyy
  have hS : i2Psi2DiffSg θ x y y' = torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) +
      torusParabolicSize (x - y) ^ (-(1 : ℝ)) + torusParabolicSize (x - y') ^ (-(1 : ℝ)) + 1 := rfl
  rw [rpow_neg_sq_eq (torusParabolicSize_nonneg _), rpow_neg_sq_eq (torusParabolicSize_nonneg _),
    rpow_neg_sq_eq (torusParabolicSize_nonneg _), rpow_neg_sq_eq (torusParabolicSize_nonneg _), hS]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A product of two sums of nonnegative numbers is at most the sum of the four squares. -/
theorem prod_add_le_sq_sum (u v u' v' : ℝ) :
    (u + v) * (u' + v') ≤ u ^ 2 + v ^ 2 + u' ^ 2 + v' ^ 2 := by
  nlinarith [sq_nonneg (u + v - u' - v'), sq_nonneg (u - v), sq_nonneg (u' - v'),
    sq_nonneg (u + v), sq_nonneg (u' + v')]

end RegularityStructures

end
