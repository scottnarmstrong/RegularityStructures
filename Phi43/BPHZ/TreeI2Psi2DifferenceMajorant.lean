/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DifferenceAlgebra

/-!
# The diagram majorants of the second difference of the chaos kernels

For the kernel increments `A, A'` of `Phi43.BPHZ.TreeI2Psi2Field`, the eight-monomial majorants
`i2Psi2Maj4`, `i2Psi2Maj2` of the chaos-`4` and chaos-`2` parts of the covariance of the
difference of two fields of `I(Ψ²) Ψ²` are rewritten as `|A| |A'|` times the monomials
(`i2Psi2Maj4_eq`, `i2Psi2Maj2_eq`). They are used in `Phi43.BPHZ.TreeI2Psi2CrossMajorant`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem rpow_neg_two_add {θ : ℝ} (hθ : 0 < θ) (u : SpaceTime) :
    torusParabolicSize u ^ (-(2 + 2 * θ)) =
      (torusParabolicSize u ^ (-(1 : ℝ))) ^ 2 * (torusParabolicSize u ^ (-θ)) ^ 2 := by
  have h0 := torusParabolicSize_nonneg u
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (torusParabolicSize u ^ (-θ)),
    ← Real.rpow_mul h0, ← Real.rpow_mul h0, ← Real.rpow_add' h0 (by push_cast; linarith)]
  congr 1
  push_cast
  ring

private theorem rpow_neg_one_add {θ : ℝ} (hθ : 0 < θ) (u : SpaceTime) :
    torusParabolicSize u ^ (-(1 + 2 * θ)) =
      torusParabolicSize u ^ (-(1 : ℝ)) * (torusParabolicSize u ^ (-θ)) ^ 2 := by
  have h0 := torusParabolicSize_nonneg u
  rw [← Real.rpow_natCast (torusParabolicSize u ^ (-θ)), ← Real.rpow_mul h0,
    ← Real.rpow_add' h0 (by push_cast; linarith)]
  congr 1
  push_cast
  ring

private theorem rpow_neg_two (u : SpaceTime) :
    torusParabolicSize u ^ (-(2 : ℝ)) = (torusParabolicSize u ^ (-(1 : ℝ))) ^ 2 := by
  have h0 := torusParabolicSize_nonneg u
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

/-- The chaos-`4` majorant as `|A| |A'|` times the monomials. -/
theorem i2Psi2Maj4_eq {θ : ℝ} (hθ : 0 < θ) (K : SpaceTime → ℝ) (x y y' w w' : SpaceTime) :
    i2Psi2Maj4 θ K x y y' (w, w') =
      |K (y - w) - K (x - w)| * |K (y' - w') - K (x - w')| *
        i2Psi2Mon4 (torusParabolicSize (w' - w) ^ (-(1 : ℝ)))
          (torusParabolicSize (y' - w) ^ (-(1 : ℝ))) (torusParabolicSize (y - w') ^ (-(1 : ℝ)))
          (torusParabolicSize (y - y') ^ (-(1 : ℝ))) (torusParabolicSize (w' - w) ^ (-θ))
          (torusParabolicSize (y' - w) ^ (-θ)) (torusParabolicSize (y - w') ^ (-θ))
          (torusParabolicSize (y - y') ^ (-θ)) := by
  unfold i2Psi2Maj4 i2Psi2Triple i2Psi2Mon4 i2Psi2Mon4a i2Psi2Mon4c i2Psi2Increment
  simp only [neg_zero, Real.rpow_zero, mul_one, one_mul, rpow_neg_two_add hθ, rpow_neg_one_add hθ,
    rpow_neg_two]
  ring

/-- The chaos-`2` majorant as `|A| |A'|` times the monomials. -/
theorem i2Psi2Maj2_eq {θ : ℝ} (hθ : 0 < θ) (K : SpaceTime → ℝ) (x y y' w w' : SpaceTime) :
    i2Psi2Maj2 θ K x y y' (w, w') =
      |K (y - w) - K (x - w)| * |K (y' - w') - K (x - w')| *
        i2Psi2Mon2 (torusParabolicSize (y - w) ^ (-(1 : ℝ)))
          (torusParabolicSize (y' - w') ^ (-(1 : ℝ))) (torusParabolicSize (w' - w) ^ (-(1 : ℝ)))
          (torusParabolicSize (y' - w) ^ (-(1 : ℝ))) (torusParabolicSize (y - w') ^ (-(1 : ℝ)))
          (torusParabolicSize (y - y') ^ (-(1 : ℝ))) (torusParabolicSize (y - w) ^ (-θ))
          (torusParabolicSize (y' - w') ^ (-θ)) (torusParabolicSize (w' - w) ^ (-θ))
          (torusParabolicSize (y' - w) ^ (-θ)) (torusParabolicSize (y - w') ^ (-θ))
          (torusParabolicSize (y - y') ^ (-θ)) := by
  unfold i2Psi2Maj2 i2Psi2Triple i2Psi2Quad i2Psi2Mon2 i2Psi2Mon2a i2Psi2Increment
  simp only [rpow_neg_one_add hθ]
  ring

end RegularityStructures.Phi43

end
