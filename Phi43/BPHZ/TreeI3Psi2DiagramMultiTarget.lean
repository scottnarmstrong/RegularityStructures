/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramTarget

/-!
# The target majorant of the difference (10.3) for `I(Ψ³)Ψ²`

`i3Psi2DiffTarget δ θ z z'` is the sum of the six pairs
`(0, -(1+δ+2θ))`, `(1-δ-2θ, -2)`, `(1-δ, -(2+2θ))`, `(-(δ+2θ), -1)`, `(-δ, -(1+2θ))`,
`(-(1+2δ+2θ), 0)` (the powers of `s(z)` or `s(z')` and of `s(z - z')`) which the diagrams of the
second difference of the covariance of the field of `I(Ψ³)Ψ²` produce.  It is the analogue of
`i3Psi2Target` with the exponents raised by `2θ` in one factor.  We prove that the bounds produced
by the weighted principal, chain, `N₁` and `N₂` diagrams are dominated by it.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The target majorant of the difference of the covariances. -/
def i3Psi2DiffTarget (δ θ : ℝ) (z z' : SpaceTime) : ℝ :=
  torusParabolicSize (z - z') ^ (-(1 + δ + 2 * θ)) +
    torusParabolicSize (z - z') ^ (-(2 : ℝ)) *
      (torusParabolicSize z ^ (1 - δ - 2 * θ) + torusParabolicSize z' ^ (1 - δ - 2 * θ)) +
    torusParabolicSize (z - z') ^ (-(2 + 2 * θ)) *
      (torusParabolicSize z ^ (1 - δ) + torusParabolicSize z' ^ (1 - δ)) +
    torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
      (torusParabolicSize z ^ (-(δ + 2 * θ)) + torusParabolicSize z' ^ (-(δ + 2 * θ))) +
    torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) *
      (torusParabolicSize z ^ (-δ) + torusParabolicSize z' ^ (-δ)) +
    torusParabolicSize z ^ (-(1 + 2 * δ + 2 * θ)) + torusParabolicSize z' ^ (-(1 + 2 * δ + 2 * θ))

end RegularityStructures

end

public section

namespace RegularityStructures

private theorem rp_nonneg (x : SpaceTime) (e : ℝ) : 0 ≤ torusParabolicSize x ^ e :=
  Real.rpow_nonneg (torusParabolicSize_nonneg _) _

theorem i3Psi2DiffTarget_nonneg (δ θ : ℝ) (z z' : SpaceTime) : 0 ≤ i3Psi2DiffTarget δ θ z z' := by
  unfold i3Psi2DiffTarget
  have a1 := rp_nonneg (z - z') (-(1 + δ + 2 * θ))
  have a2 := mul_nonneg (rp_nonneg (z - z') (-(2 : ℝ)))
    (add_nonneg (rp_nonneg z (1 - δ - 2 * θ)) (rp_nonneg z' (1 - δ - 2 * θ)))
  have a3 := mul_nonneg (rp_nonneg (z - z') (-(2 + 2 * θ)))
    (add_nonneg (rp_nonneg z (1 - δ)) (rp_nonneg z' (1 - δ)))
  have a4 := mul_nonneg (rp_nonneg (z - z') (-(1 : ℝ)))
    (add_nonneg (rp_nonneg z (-(δ + 2 * θ))) (rp_nonneg z' (-(δ + 2 * θ))))
  have a5 := mul_nonneg (rp_nonneg (z - z') (-(1 + 2 * θ)))
    (add_nonneg (rp_nonneg z (-δ)) (rp_nonneg z' (-δ)))
  have a6 := rp_nonneg z (-(1 + 2 * δ + 2 * θ))
  have a7 := rp_nonneg z' (-(1 + 2 * δ + 2 * θ))
  linarith

/-- The principal pair with the raised Hölder loss. -/
theorem principal_raised_le_diffTarget (δ θ : ℝ) (z z' : SpaceTime) :
    torusParabolicSize (z - z') ^ (-(2 : ℝ)) * torusParabolicSize z' ^ (1 - δ - 2 * θ) ≤
      i3Psi2DiffTarget δ θ z z' := by
  have h := i3Psi2DiffTarget_nonneg δ θ z z'
  unfold i3Psi2DiffTarget at h ⊢
  have a1 := rp_nonneg (z - z') (-(1 + δ + 2 * θ))
  have a2 := mul_nonneg (rp_nonneg (z - z') (-(2 : ℝ))) (rp_nonneg z (1 - δ - 2 * θ))
  have a3 := mul_nonneg (rp_nonneg (z - z') (-(2 + 2 * θ)))
    (add_nonneg (rp_nonneg z (1 - δ)) (rp_nonneg z' (1 - δ)))
  have a4 := mul_nonneg (rp_nonneg (z - z') (-(1 : ℝ)))
    (add_nonneg (rp_nonneg z (-(δ + 2 * θ))) (rp_nonneg z' (-(δ + 2 * θ))))
  have a5 := mul_nonneg (rp_nonneg (z - z') (-(1 + 2 * θ)))
    (add_nonneg (rp_nonneg z (-δ)) (rp_nonneg z' (-δ)))
  have a6 := rp_nonneg z (-(1 + 2 * δ + 2 * θ))
  have a7 := rp_nonneg z' (-(1 + 2 * δ + 2 * θ))
  rw [mul_add] at *
  linarith

/-- The principal pair with the raised exponent of the covariance of the points. -/
theorem principal_far_le_diffTarget (δ θ : ℝ) (z z' : SpaceTime) :
    torusParabolicSize (z - z') ^ (-(2 + 2 * θ)) * torusParabolicSize z' ^ (1 - δ) ≤
      i3Psi2DiffTarget δ θ z z' := by
  unfold i3Psi2DiffTarget
  have a1 := rp_nonneg (z - z') (-(1 + δ + 2 * θ))
  have a2 := mul_nonneg (rp_nonneg (z - z') (-(2 : ℝ)))
    (add_nonneg (rp_nonneg z (1 - δ - 2 * θ)) (rp_nonneg z' (1 - δ - 2 * θ)))
  have a3 := mul_nonneg (rp_nonneg (z - z') (-(2 + 2 * θ))) (rp_nonneg z (1 - δ))
  have a4 := mul_nonneg (rp_nonneg (z - z') (-(1 : ℝ)))
    (add_nonneg (rp_nonneg z (-(δ + 2 * θ))) (rp_nonneg z' (-(δ + 2 * θ))))
  have a5 := mul_nonneg (rp_nonneg (z - z') (-(1 + 2 * θ)))
    (add_nonneg (rp_nonneg z (-δ)) (rp_nonneg z' (-δ)))
  have a6 := rp_nonneg z (-(1 + 2 * δ + 2 * θ))
  have a7 := rp_nonneg z' (-(1 + 2 * δ + 2 * θ))
  rw [mul_add] at *
  linarith

/-- The chain pair with the raised total exponent. -/
theorem chain_raised_le_diffTarget {δ θ : ℝ} {z z' : SpaceTime}
    (hx : 0 < torusParabolicSize (z - z')) :
    torusParabolicSize (z - z') ^ (-(1 : ℝ)) * i3Psi2S (δ + 2 * θ) z z' ≤
      i3Psi2DiffTarget δ θ z z' := by
  have e : torusParabolicSize (z - z') ^ (-(1 : ℝ)) * torusParabolicSize (z - z') ^ (-(δ + 2 * θ)) =
      torusParabolicSize (z - z') ^ (-(1 + δ + 2 * θ)) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  unfold i3Psi2S i3Psi2DiffTarget
  simp only [sub_zero]
  have a2 := mul_nonneg (rp_nonneg (z - z') (-(2 : ℝ)))
    (add_nonneg (rp_nonneg z (1 - δ - 2 * θ)) (rp_nonneg z' (1 - δ - 2 * θ)))
  have a3 := mul_nonneg (rp_nonneg (z - z') (-(2 + 2 * θ)))
    (add_nonneg (rp_nonneg z (1 - δ)) (rp_nonneg z' (1 - δ)))
  have a5 := mul_nonneg (rp_nonneg (z - z') (-(1 + 2 * θ)))
    (add_nonneg (rp_nonneg z (-δ)) (rp_nonneg z' (-δ)))
  have a6 := rp_nonneg z (-(1 + 2 * δ + 2 * θ))
  have a7 := rp_nonneg z' (-(1 + 2 * δ + 2 * θ))
  rw [mul_add, mul_add, e]
  rw [mul_add] at *
  linarith

/-- The chain pair with the raised exponent of the covariance of the points. -/
theorem chain_far_le_diffTarget {δ θ : ℝ} {z z' : SpaceTime}
    (hx : 0 < torusParabolicSize (z - z')) :
    torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) * i3Psi2S δ z z' ≤
      i3Psi2DiffTarget δ θ z z' := by
  have e : torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) * torusParabolicSize (z - z') ^ (-δ) =
      torusParabolicSize (z - z') ^ (-(1 + δ + 2 * θ)) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  unfold i3Psi2S i3Psi2DiffTarget
  simp only [sub_zero]
  have a2 := mul_nonneg (rp_nonneg (z - z') (-(2 : ℝ)))
    (add_nonneg (rp_nonneg z (1 - δ - 2 * θ)) (rp_nonneg z' (1 - δ - 2 * θ)))
  have a3 := mul_nonneg (rp_nonneg (z - z') (-(2 + 2 * θ)))
    (add_nonneg (rp_nonneg z (1 - δ)) (rp_nonneg z' (1 - δ)))
  have a4 := mul_nonneg (rp_nonneg (z - z') (-(1 : ℝ)))
    (add_nonneg (rp_nonneg z (-(δ + 2 * θ))) (rp_nonneg z' (-(δ + 2 * θ))))
  have a6 := rp_nonneg z (-(1 + 2 * δ + 2 * θ))
  have a7 := rp_nonneg z' (-(1 + 2 * δ + 2 * θ))
  rw [mul_add, mul_add, e]
  rw [mul_add] at *
  linarith

/-- The `N₁`, `N₂` bounds `S_{1+δ+2θ}`. -/
theorem S_one_add_le_diffTarget {δ θ : ℝ} (hδ : 0 < δ) {z z' : SpaceTime}
    (hz : 0 < torusParabolicSize z) (hz' : 0 < torusParabolicSize z')
    (hz1 : torusParabolicSize z ≤ 1) (hz1' : torusParabolicSize z' ≤ 1) :
    i3Psi2S (1 + δ + 2 * θ) z z' ≤ i3Psi2DiffTarget δ θ z z' := by
  have e1 : torusParabolicSize z ^ (-(1 + δ + 2 * θ)) ≤ torusParabolicSize z ^ (-(1 + 2 * δ + 2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hz hz1 (by linarith)
  have e2 : torusParabolicSize z' ^ (-(1 + δ + 2 * θ)) ≤
      torusParabolicSize z' ^ (-(1 + 2 * δ + 2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hz' hz1' (by linarith)
  unfold i3Psi2S i3Psi2DiffTarget
  simp only [sub_zero]
  have a2 := mul_nonneg (rp_nonneg (z - z') (-(2 : ℝ)))
    (add_nonneg (rp_nonneg z (1 - δ - 2 * θ)) (rp_nonneg z' (1 - δ - 2 * θ)))
  have a3 := mul_nonneg (rp_nonneg (z - z') (-(2 + 2 * θ)))
    (add_nonneg (rp_nonneg z (1 - δ)) (rp_nonneg z' (1 - δ)))
  have a4 := mul_nonneg (rp_nonneg (z - z') (-(1 : ℝ)))
    (add_nonneg (rp_nonneg z (-(δ + 2 * θ))) (rp_nonneg z' (-(δ + 2 * θ))))
  have a5 := mul_nonneg (rp_nonneg (z - z') (-(1 + 2 * θ)))
    (add_nonneg (rp_nonneg z (-δ)) (rp_nonneg z' (-δ)))
  linarith

/-- The pair `(0, -(1+δ+2θ))`. -/
theorem far_le_diffTarget (δ θ : ℝ) (z z' : SpaceTime) :
    torusParabolicSize (z - z') ^ (-(1 + δ + 2 * θ)) ≤ i3Psi2DiffTarget δ θ z z' := by
  unfold i3Psi2DiffTarget
  have a2 := mul_nonneg (rp_nonneg (z - z') (-(2 : ℝ)))
    (add_nonneg (rp_nonneg z (1 - δ - 2 * θ)) (rp_nonneg z' (1 - δ - 2 * θ)))
  have a3 := mul_nonneg (rp_nonneg (z - z') (-(2 + 2 * θ)))
    (add_nonneg (rp_nonneg z (1 - δ)) (rp_nonneg z' (1 - δ)))
  have a4 := mul_nonneg (rp_nonneg (z - z') (-(1 : ℝ)))
    (add_nonneg (rp_nonneg z (-(δ + 2 * θ))) (rp_nonneg z' (-(δ + 2 * θ))))
  have a5 := mul_nonneg (rp_nonneg (z - z') (-(1 + 2 * θ)))
    (add_nonneg (rp_nonneg z (-δ)) (rp_nonneg z' (-δ)))
  have a6 := rp_nonneg z (-(1 + 2 * δ + 2 * θ))
  have a7 := rp_nonneg z' (-(1 + 2 * δ + 2 * θ))
  linarith

/-- The pair `(-(1+2δ+2θ), 0)` at `z`. -/
theorem left_le_diffTarget (δ θ : ℝ) (z z' : SpaceTime) :
    torusParabolicSize z ^ (-(1 + 2 * δ + 2 * θ)) ≤ i3Psi2DiffTarget δ θ z z' := by
  unfold i3Psi2DiffTarget
  have a1 := rp_nonneg (z - z') (-(1 + δ + 2 * θ))
  have a2 := mul_nonneg (rp_nonneg (z - z') (-(2 : ℝ)))
    (add_nonneg (rp_nonneg z (1 - δ - 2 * θ)) (rp_nonneg z' (1 - δ - 2 * θ)))
  have a3 := mul_nonneg (rp_nonneg (z - z') (-(2 + 2 * θ)))
    (add_nonneg (rp_nonneg z (1 - δ)) (rp_nonneg z' (1 - δ)))
  have a4 := mul_nonneg (rp_nonneg (z - z') (-(1 : ℝ)))
    (add_nonneg (rp_nonneg z (-(δ + 2 * θ))) (rp_nonneg z' (-(δ + 2 * θ))))
  have a5 := mul_nonneg (rp_nonneg (z - z') (-(1 + 2 * θ)))
    (add_nonneg (rp_nonneg z (-δ)) (rp_nonneg z' (-δ)))
  have a7 := rp_nonneg z' (-(1 + 2 * δ + 2 * θ))
  linarith

/-- The pair `(-(1+2δ+2θ), 0)` at `z'`. -/
theorem right_le_diffTarget (δ θ : ℝ) (z z' : SpaceTime) :
    torusParabolicSize z' ^ (-(1 + 2 * δ + 2 * θ)) ≤ i3Psi2DiffTarget δ θ z z' := by
  unfold i3Psi2DiffTarget
  have a1 := rp_nonneg (z - z') (-(1 + δ + 2 * θ))
  have a2 := mul_nonneg (rp_nonneg (z - z') (-(2 : ℝ)))
    (add_nonneg (rp_nonneg z (1 - δ - 2 * θ)) (rp_nonneg z' (1 - δ - 2 * θ)))
  have a3 := mul_nonneg (rp_nonneg (z - z') (-(2 + 2 * θ)))
    (add_nonneg (rp_nonneg z (1 - δ)) (rp_nonneg z' (1 - δ)))
  have a4 := mul_nonneg (rp_nonneg (z - z') (-(1 : ℝ)))
    (add_nonneg (rp_nonneg z (-(δ + 2 * θ))) (rp_nonneg z' (-(δ + 2 * θ))))
  have a5 := mul_nonneg (rp_nonneg (z - z') (-(1 + 2 * θ)))
    (add_nonneg (rp_nonneg z (-δ)) (rp_nonneg z' (-δ)))
  have a6 := rp_nonneg z (-(1 + 2 * δ + 2 * θ))
  linarith

end RegularityStructures

end
