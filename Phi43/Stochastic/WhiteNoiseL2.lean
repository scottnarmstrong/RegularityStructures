/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.WhiteNoiseLinearity

/-!
# The `L²` isometry identity for white-noise pairings

Almost-sure linearity of a Gaussian white-noise family gives the exact distance formula

`E |W h - W g|² = ∫ (h - g)²`.

This is the deterministic-to-annealed continuity interface used by heat-kernel approximations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

theorem whiteNoise_pairing_sub_ae (hW : IsWhiteNoise P W)
    {h g : SpaceTime → ℝ} (hh : MemLp h 2) (hg : MemLp g 2) :
    (fun ω => W h ω - W g ω) =ᵐ[P] W (h - g) := by
  have hsub : MemLp (h - g) 2 := hh.sub hg
  have hadd := whiteNoise_add_ae_fun hW hsub hg
  have hfun : (h - g) + g = h := by
    funext z
    change h z - g z + g z = h z
    ring
  have hadd' : W h =ᵐ[P] fun ω => W (h - g) ω + W g ω := by
    simpa [hfun] using hadd
  filter_upwards [hadd'] with ω hω
  linarith

end RegularityStructures

end
