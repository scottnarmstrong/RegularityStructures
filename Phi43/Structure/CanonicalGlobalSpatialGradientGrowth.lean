/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSpatialSecondDerivativeGrowth

/-!
# Growth of the actual integrated spatial gradient

This is the direct convolution consequence of the smooth-noise second-spatial
derivative envelope.  It is a source-derived component of Hairer’s global
Gamma estimate [Hai14, Proposition 8.27].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open scoped ContDiff

theorem canonicalGlobalSpatialGradient_fderiv_growth
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ q)
    (i : Fin 3) :
    PolyBounded (fun z => ‖fderiv ℝ
      (hairerSpatialGradient N noise.zeta i) z‖) := by
  have hκ : κ = κ := rfl
  cases hκ
  exact canonicalPolyBounded_fderiv_hairerSpatialGradient N noise.smooth i
    (canonicalNoise_spatialDerivative_fderiv_growth noise C q hg i)

end RegularityStructures.Phi43

end
