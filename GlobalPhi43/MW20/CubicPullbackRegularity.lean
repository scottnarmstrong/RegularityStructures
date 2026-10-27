module

public import GlobalPhi43.MW20.HeatRescaling
public import GlobalPhi43.MW20.CubicRegularity
public import RegularityStructures.Analysis.Parabolic.TestFunction
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Local regularity and exact interior containment of cubic pullbacks
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- The parabolic affine coordinate map is smooth. -/
theorem contDiff_sourceAffine (b : ParabolicSpace) (c : ℝ) :
    ContDiff ℝ 2 (fun z => b + parabolicDilate c z) := by
  simpa only [parabolicDilateCLM_apply] using!
    (contDiff_const.add (parabolicDilateCLM c).contDiff :
      ContDiff ℝ 2 (fun z => b + parabolicDilateCLM c z))

/-- Regularity of the actual pullback is derived from the tested C² germs. -/
theorem sourceCubicRegularity_pullback (w : ParabolicSpace → ℝ) (b : ParabolicSpace)
    (c : ℝ) (hw : ∀ z ∈ sourceClosedCylinder,
      ContDiffAt ℝ 2 w (b + parabolicDilate c z)) :
    SourceCubicRegularity (sourceCubicPullback w b c) := by
  have hc : ∀ z ∈ sourceClosedCylinder, ContDiffAt ℝ 2 (sourceCubicPullback w b c) z := by
    intro z hz
    exact contDiffAt_const.mul ((hw z hz).comp z (contDiff_sourceAffine b c).contDiffAt)
  refine ⟨fun z hz => (hc z hz).continuousAt.continuousWithinAt, ?_⟩
  intro z ht ht1 hx
  apply hc z
  exact ⟨⟨ht.le, fun i => (hx i).1.le⟩, ⟨ht1, fun i => (hx i).2.le⟩⟩

/-- The complete closed unit cylinder around an interior point stays inside
the larger source cylinder. The time window is exactly the squared gap. -/
theorem cubicPullback_sourceCylinder {R S : ℝ} (hS : 0 ≤ S) (hSR : S < R)
    {x z : ParabolicSpace} (hx : x ∈ sourceCylinder R)
    (hz : z ∈ sourceClosedCylinder) :
    (x.1 - (R - S) ^ 2, x.2) + parabolicDilate (R - S) z ∈ sourceCylinder S := by
  have hc : 0 < R - S := sub_pos.mpr hSR
  change S ^ 2 < x.1 - (R - S) ^ 2 + (R - S) ^ 2 * z.1 ∧
    x.1 - (R - S) ^ 2 + (R - S) ^ 2 * z.1 < 1 ∧
    ∀ i, |x.2 i + (R - S) * z.2 i| < 1 - S
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hx.1, hz.1.1, mul_nonneg (sq_nonneg (R - S)) hz.1.1,
      mul_nonneg hS (sub_nonneg.mpr hSR.le)]
  · nlinarith [hx.2.1, hz.2.1, mul_nonneg (sq_nonneg (R - S)) (sub_nonneg.mpr hz.2.1)]
  · intro i
    have hi : |z.2 i| ≤ 1 := abs_le.mpr ⟨hz.1.2 i, hz.2.2 i⟩
    have hm : |(R - S) * z.2 i| ≤ R - S := by
      rw [abs_mul, abs_of_pos hc]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hi hc.le
    exact (abs_add_le _ _).trans_lt (by linarith [hx.2.2 i])

end GlobalPhi43.MW20
