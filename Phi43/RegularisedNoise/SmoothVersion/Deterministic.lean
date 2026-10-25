/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.Properties
public import RegularityStructures.Probability.SpaceTimeMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Deterministic input for smooth white-noise modifications

A smooth function on space-time which is supported in a bounded time interval is compactly
supported because the spatial torus is compact.  This file records the resulting `L²` facts used
by the smooth-version construction.  The support argument is independent of the periodisation
facts for the mollifier.
-/

@[expose] public section

open MeasureTheory Set

namespace RegularityStructures.Phi43

theorem hasCompactSupport_of_isSmoothOnSpaceTime_of_timeSupport
    {Phi : SpaceTime → ℝ} {R : ℝ}
    (_hPhi : IsSmoothOnSpaceTime Phi)
    (hR : ∀ z, R < |z.1| → Phi z = 0) :
    HasCompactSupport Phi := by
  by_cases hR0 : 0 ≤ R
  · apply HasCompactSupport.intro' (isCompact_Icc.prod isCompact_univ)
      (isClosed_Icc.prod isClosed_univ)
    rintro ⟨t, x⟩ htx
    apply hR
    have ht : t ∉ Icc (-R) R := by
      intro ht
      exact htx ⟨ht, mem_univ x⟩
    by_cases hlow : -R ≤ t
    · have ht : R < t := lt_of_not_ge (fun hupper => ht ⟨hlow, hupper⟩)
      by_cases ht0 : 0 ≤ t
      · rw [abs_of_nonneg ht0]
        exact ht
      · exact False.elim (ht0 (by linarith [hR0, ht]))
    · have ht : t < -R := lt_of_not_ge hlow
      by_cases ht0 : 0 ≤ t
      · exfalso
        linarith [hR0, ht0]
      · rw [abs_of_nonpos (le_of_not_ge ht0)]
        linarith
  · have hzero : Phi = 0 := by
      funext z
      apply hR
      exact lt_of_not_ge hR0 |>.trans_le (abs_nonneg z.1)
    rw [hzero]
    exact HasCompactSupport.zero

theorem memLp_of_isSmoothOnSpaceTime_of_timeSupport
    {Phi : SpaceTime → ℝ} {R : ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    (hR : ∀ z, R < |z.1| → Phi z = 0) :
    MemLp Phi 2 (volume : Measure SpaceTime) := by
  exact (Continuous.continuous_of_isSmoothOnSpaceTime hPhi).memLp_of_hasCompactSupport
    (hasCompactSupport_of_isSmoothOnSpaceTime_of_timeSupport hPhi hR)

theorem memLp_translate_of_isSmoothOnSpaceTime_of_timeSupport
    {Phi : SpaceTime → ℝ} {R : ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    (hR : ∀ z, R < |z.1| → Phi z = 0) (z : SpaceTime) :
    MemLp (fun w => Phi (z - w)) 2 (volume : Measure SpaceTime) :=
  memLp_comp_sub_left_spaceTime
    (memLp_of_isSmoothOnSpaceTime_of_timeSupport hPhi hR) z

end RegularityStructures.Phi43

end
