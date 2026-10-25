/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.QFamilyR4ModelBound
public import RegularityStructures.Abstract.FixedPointTimeSlab

/-!
# Hairer's time window and window model bounds

`hairerTimeWindow = {z | -1 ≤ z.1 ≤ 2}` is the window `O = [-1, 2] × ℝ³` of [Hai14, Thm 7.1].
If `z` has time coordinate in `[0, 1]` (in particular for `z` in the slab `(0, T]`, `T ≤ 1`),
the whole closed parabolic ball `{y | ‖y - z‖_𝔰 ≤ 1}` lies in the window
(`ball_subset_hairerTimeWindow`). The convenience lemma `abs_gammaMap_single_le_of_window` is the
bound `|(Γ_{yx} e_i)_j| ≤ C_Γ d(y, x)^{deg i - deg j}` for `x, y` in the window.

`Model.HasQualitativeGrowth M γ` is the purely qualitative polynomial growth of the
regularisations `Q_t Π_x e_i` (for `deg i < γ`, `0 < t ≤ 1`); the constants are never used
quantitatively, only for the existence of pairings.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 7.1, (2.15).
-/

@[expose] public section

namespace RegularityStructures

/-- Hairer's window `O = [-1, 2] × ℝ³` of [Hai14, Theorem 7.1]. -/
def hairerTimeWindow : Set ParabolicSpace := {z | -1 ≤ z.1 ∧ z.1 ≤ 2}

end RegularityStructures

end

public section

open Set

namespace RegularityStructures

theorem abs_time_sub_le_of_parabolicNorm_le {w : ParabolicSpace} {r : ℝ}
    (h : parabolicNorm w ≤ r) : |w.1| ≤ r ^ 2 := by
  have h1 : Real.sqrt |w.1| ≤ parabolicNorm w := by
    unfold parabolicNorm
    have : 0 ≤ ∑ i, |w.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have h2 : Real.sqrt |w.1| ≤ r := h1.trans h
  have h3 := Real.sq_sqrt (abs_nonneg w.1)
  have h0 : 0 ≤ Real.sqrt |w.1| := Real.sqrt_nonneg _
  nlinarith

/-- For `z` with `0 ≤ z.1 ≤ 1` the closed parabolic ball of radius `1` about `z` lies in the
window. In particular this holds for every base point of the slab `(0, T]`, `T ≤ 1`. -/
theorem ball_subset_hairerTimeWindow {z : ParabolicSpace} (hz0 : 0 ≤ z.1) (hz1 : z.1 ≤ 1)
    {y : ParabolicSpace} (hy : parabolicNorm (y - z) ≤ 1) : y ∈ hairerTimeWindow := by
  have h := abs_time_sub_le_of_parabolicNorm_le hy
  have h2 : |y.1 - z.1| ≤ 1 := by simpa using h
  obtain ⟨h3, h4⟩ := abs_le.1 h2
  exact ⟨by linarith, by linarith⟩

theorem mem_hairerTimeWindow_of_mem_timeSlab {T : ℝ} (hT : T ≤ 1) {z : ParabolicSpace}
    (hz : z ∈ timeSlab T) : z ∈ hairerTimeWindow := by
  have := hz
  simp only [timeSlab, Set.mem_ofPred_eq] at this
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

end RegularityStructures

end
