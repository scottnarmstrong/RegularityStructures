/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsCovariance
public import RegularityStructures.Torus.KernelBoundsGeometry
public import RegularityStructures.Probability.SpaceTimeMeasure
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrals of parabolic power weights

For a real exponent `p`, the weights `s(z)^(-p)` restricted to the ball `s ≤ a`
(`singularLocalWeight`) or to the exterior `s > e` (`singularTailWeight`) have integrals
of order `a^(5-p)` (for `p < 5`) and `e^(5-p)` (for `p > 5`) on space-time, the homogeneous
dimension being five.  The proofs use the layer-cake formula and the global ball-volume bound.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

/-- The power weight `s(z)^(-p)` restricted to the punctured ball `0 < s(z) ≤ a`. -/
def singularLocalWeight (p a : ℝ) (z : SpaceTime) : ℝ :=
  if 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ a then
    torusParabolicSize z ^ (-p) else 0

/-- The power weight `s(z)^(-p)` restricted to the exterior `e < s(z)`. -/
def singularTailWeight (p e : ℝ) (z : SpaceTime) : ℝ :=
  if e < torusParabolicSize z then torusParabolicSize z ^ (-p) else 0

end RegularityStructures

end
