/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.ProbeDerivative

/-! Continuity extends the past-ball approximation to its centre. -/
public noncomputable section

namespace GlobalPhi43.Local

open Filter RegularityStructures
open scoped Topology

/-- The intercept is controlled by the approximation error at every radius,
although the centre itself is excluded from the strict past ball. -/
theorem affine_intercept_bound (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (c : ℝ) (ν : Fin 3 → ℝ) {R E : ℝ} (hR : 0 < R)
    (hf : ContinuousAt f x)
    (happrox : ∀ y ∈ pastBall x R, |f y - spatialAffine x c ν y| ≤ E) :
    |f x - c| ≤ E := by
  have hv : Tendsto (fun s : ℝ => verticalProbe x s) (𝓝[>] 0) (𝓝 x) := by
    simpa [verticalProbe] using (verticalProbe_hasDerivAt x).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ => |f (verticalProbe x s) - c|) (𝓝[>] 0) (𝓝 |f x - c|) :=
    ((hf.tendsto.comp hv).sub_const c).abs
  apply le_of_tendsto hlim
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hlt : ∀ᶠ s : ℝ in 𝓝[>] 0, s < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, hlt] with s hs hsR
  have h := happrox (verticalProbe x s) (verticalProbe_past hs hsR)
  simpa [spatialAffine, spatialLinear, verticalProbe] using h

end GlobalPhi43.Local
