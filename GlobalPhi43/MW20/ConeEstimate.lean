/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

/-!
# Pointwise cone estimate from MW20 Corollary 2.12

This is the triangle-inequality part of the proof of (2.37), with an explicit
positive radius. The geometric cone witness and the seminorm bounds are premises
here; construction of those objects and (2.38) are not claimed by this module.
-/

public section

namespace GlobalPhi43.MW20

/-- Pointwise form of (2.37), once the cone witness has been chosen. The scalar
`p` is the spatial affine correction evaluated at that witness, and `u` is the
corresponding value of the two-point remainder. -/
theorem cone_estimate_at_positive_radius {r κ lam n A M u p : ℝ}
    (hr : 0 < r) (hcone : lam * n * r ≤ |p|)
    (hremainder : |u - p| ≤ A * r ^ κ) (hU : |u| ≤ M) :
    lam * n ≤ A * r ^ (κ - 1) + M / r := by
  have htriangle : |p| ≤ |u - p| + |u| := by
    calc
      |p| = |-(u - p) + u| := by congr 1; ring
      _ ≤ |-(u - p)| + |u| := abs_add_le _ _
      _ = |u - p| + |u| := by rw [abs_neg]
  have hbound : lam * n * r ≤ A * r ^ κ + M :=
    hcone.trans (htriangle.trans (add_le_add hremainder hU))
  have hdiv := (le_div_iff₀ hr).2 hbound
  rw [Real.rpow_sub_one hr.ne']
  simpa only [add_div, mul_div_assoc] using hdiv

end GlobalPhi43.MW20

end
