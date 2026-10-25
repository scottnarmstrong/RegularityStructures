/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.AnnealedNoise

/-!
# The stochastic bridge for mollified test functions

For a kernel `k` and a test function `g`, this file defines the pairing through `W` applied to the
space-time convolution.  The theorem below proves the annealed estimate from the uniform `L²`
bound on that convolved test function.  Establishing that bound for the torus-periodised
rescaled test functions is an analytic periodisation theorem and is intentionally an explicit
hypothesis here; it cannot be inferred from `IsWhiteNoise` alone.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

/-- Convolution of a space-time kernel with a test function. -/
def spaceTimeConvolution (k g : SpaceTime → ℝ) : SpaceTime → ℝ :=
  fun x => ∫ y, k y * g (x - y)

end RegularityStructures

end
