/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SingularConvolutionLayer

/-!
# Mass of a power singularity on a set of finite volume

For `0 < p < 5`, `lam > 0` and a measurable set `K` of finite volume, the integral of
`s(u - v)^(-p)` over `v ∈ K` is at most `80/(5-p) lam^(5-p) + lam^(-p) vol(K)`.  Near the
singularity (`s ≤ lam`) the layer-cake bound for `singularLocalWeight` applies; away from it the
weight is at most `lam^(-p)`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- The reflected parabolic size is almost everywhere positive. -/
theorem treePsi_ae_pos_size_sub (u : SpaceTime) :
    ∀ᵐ v : SpaceTime ∂volume, 0 < torusParabolicSize (u - v) := by
  have h0 : volume {z : SpaceTime | torusParabolicSize z ≤ 0} = 0 := by
    have h := Phi43.volume_torusParabolicBall_le_global (le_refl (0 : ℝ))
    exact nonpos_iff_eq_zero.1 (by simpa using h)
  have hae : ∀ᵐ w : SpaceTime ∂volume, 0 < torusParabolicSize w := by
    rw [ae_iff]
    refine measure_mono_null ?_ h0
    intro w hw
    exact not_lt.1 hw
  exact (measurePreserving_sub_left_spaceTime u).quasiMeasurePreserving.ae hae

end RegularityStructures

end
