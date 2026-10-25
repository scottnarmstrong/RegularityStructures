/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.WhiteNoiseL2

/-!
# Covariance of two white-noise pairings

The finite-dimensional definition of white noise gives the covariance identity for any two
square-integrable test functions.  This is the scalar identity used by the stochastic Fubini
argument for the heat-regularised field.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem whiteNoise_pairing_mul_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {h g : SpaceTime → ℝ}
    (hh : MemLp h 2) (hg : MemLp g 2) :
    ∫ ω, W h ω * W g ω ∂P = ∫ z, h z * g z := by
  have hvec := hW.2 2 ![h, g] (by
    intro i
    fin_cases i
    · simpa using hh
    · simpa using hg)
  simpa using hvec.2.2.2 0 1

end RegularityStructures

end
