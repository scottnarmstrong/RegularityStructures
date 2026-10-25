/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalModelData
public import RegularityStructures.Abstract.Polynomial.Model.Growth

/-!
# Explicit polynomial derivative growth for smooth canonical models

The polynomially weighted framework of Hoshino [Hos25, Definition 2.1,
(2.1)–(2.2)] permits whole-space Q regularisation. The explicit derivative
inequality below is the growth hypothesis imposed on the smooth noise.
It is not an analytic bound on the model: the model and its causal admissibility
are constructed and proved. No time cutoff or localisation is used.

Source for the lift and admissibility: Hairer [Hai14, Proposition 8.27,
Definition 5.9, (8.18)–(8.20)]. Compact positive-sector Q bounds are separate.
-/

public section

namespace RegularityStructures.Phi43

/-- The zeroth derivative in the explicit growth inequality controls Q tails. -/
theorem canonicalNoise_polyBounded_of_derivatives (noise : CanonicalNoise)
    (C : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ p) :
    PolyBounded noise.zeta := by
  refine ⟨noise.smooth.continuous.measurable, C, p, fun z => ?_⟩
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hg 0 (by omega) z

end RegularityStructures.Phi43

end

