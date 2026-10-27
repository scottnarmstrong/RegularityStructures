/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AffineCentre
public import GlobalPhi43.Local.LargeRemainder

/-! Passing a past-ball approximation to a common coefficient. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped BigOperators

/-- The intercept is paid by the same approximation error, and the spatial
coefficient tail by its actual sup norm. -/
theorem remainder_of_affine_approximation
    (f : ParabolicSpace → ℝ) (x : ParabolicSpace) (c : ℝ) (ν a : Fin 3 → ℝ)
    {R E T : ℝ} (hR : 0 < R) (hf : ContinuousAt f x) (hzero : f x = 0)
    (happrox : ∀ y ∈ pastBall x R, |f y - spatialAffine x c ν y| ≤ E)
    (htail : ‖ν - a‖ ≤ T) {y : ParabolicSpace} (hy : y ∈ pastBall x R) :
    |f y - spatialLinear a (y - x)| ≤ 2 * E + 3 * T * R := by
  have hc : |c| ≤ E := by
    simpa only [hzero, zero_sub, abs_neg] using affine_intercept_bound f x c ν hR hf happrox
  have hT : 0 ≤ T := (norm_nonneg _).trans htail
  have hl := spatialLinear_abs_le (ν - a) x y hT (fun i => by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using (norm_le_pi_norm (ν - a) i).trans htail)
  have heq : f y - spatialLinear a (y - x) =
      (f y - spatialAffine x c ν y) + c + spatialLinear (ν - a) (y - x) := by
    simp only [spatialAffine, spatialLinear, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  calc
    _ ≤ |f y - spatialAffine x c ν y| + |c| + |spatialLinear (ν - a) (y - x)| := by
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ E + E + 3 * T * R := add_le_add (add_le_add (happrox y hy) hc)
      (hl.trans (mul_le_mul_of_nonneg_left hy.1.le (by positivity)))
    _ = _ := by ring

end GlobalPhi43.Local
