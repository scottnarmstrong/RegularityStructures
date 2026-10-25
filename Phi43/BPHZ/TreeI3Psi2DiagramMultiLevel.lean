/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramLevel
public import Phi43.BPHZ.TreeI3PsiDiagramMultiBasic

/-!
# Two-level majorants: domination and measurable weights

`TwoLevelLe.of_le`: a nonnegative function `G'` with measurable slices which is dominated almost
everywhere by a two-level majorant `G` is again a two-level majorant with the same bound.  This lets
us state the bounds of the weighted diagrams of `I(Ψ³)Ψ²` for the weight itself, so that bounds for
sums of weights follow from `TwoLevelLe.add` and `TwoLevelLe.const_mul`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- A two-level majorant dominates every nonnegative function with measurable slices below it. -/
theorem TwoLevelLe.of_le {G G' : SpaceTime → SpaceTime → ℝ} {X : ℝ} (hG : TwoLevelLe G X)
    (hm : ∀ w, Measurable (G' w)) (h0 : ∀ w v, 0 ≤ G' w v)
    (hle : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, G' w v ≤ G w v) :
    TwoLevelLe G' X := by
  obtain ⟨h1, H, hH, hGH⟩ := hG
  refine ⟨?_, H, hH, ?_⟩
  · filter_upwards [h1, hle] with w a b
    refine a.mono' (hm w).aestronglyMeasurable ?_
    filter_upwards [b] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 w v)]
    exact hv
  · filter_upwards [h1, hle, hGH] with w a b c
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (h0 w)) a ?_).trans c
    exact b

/-- The two-level majorant built from `hg`, `hH` of `integrable_and_abs_le_of_majorant`. -/
theorem twoLevelLe_of_inner {m : SpaceTime → ℝ} {g : SpaceTime → SpaceTime → ℝ} {V : SpaceTime → ℝ}
    {X : ℝ} (hm : ∀ w, 0 ≤ m w) (hg : ∀ᵐ w : SpaceTime ∂volume, SingularIntLe (g w) (V w))
    (hH : SingularIntLe (fun w => m w * V w) X) :
    TwoLevelLe (fun w v => m w * g w v) X := by
  refine ⟨?_, fun w => m w * V w, hH, ?_⟩
  · filter_upwards [hg] with w h using h.1.const_mul (m w)
  · filter_upwards [hg] with w h
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left h.2 (hm w)

end RegularityStructures

end
