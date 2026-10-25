/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Basic
public import RegularityStructures.Analysis.Heat.Decomposition.LineIter

/-!
# Compact support of the heat shells

The closed parabolic ball `{‖z‖_𝔰 ≤ r}` is compact, so each `heatShell n` is smooth with compact
support and every `lineIter` of it is bounded.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem isCompact_parabolicNorm_le (r : ℝ) : IsCompact {z : ParabolicSpace | parabolicNorm z ≤ r} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_parabolicNorm
    continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ParabolicSpace)) (r := max r (r ^ 2))).subset ?_
  intro z hz
  have hz' : parabolicNorm z ≤ r := hz
  have hn := parabolicNorm_nonneg z
  have h0 : |z.1| ≤ parabolicNorm z ^ 2 := by
    have : Real.sqrt |z.1| ≤ parabolicNorm z := by
      unfold parabolicNorm
      have : 0 ≤ ∑ i, |z.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    calc |z.1| = Real.sqrt |z.1| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
      _ ≤ _ := by gcongr
  have hi : ∀ i, |z.2 i| ≤ parabolicNorm z := fun i => by
    unfold parabolicNorm
    have : |z.2 i| ≤ ∑ j, |z.2 j| :=
      Finset.single_le_sum (f := fun j => |z.2 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [Real.sqrt_nonneg |z.1|]
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  refine max_le_iff.2 ⟨?_, ?_⟩
  · refine le_trans ?_ (le_max_right _ _)
    rw [Real.norm_eq_abs]
    exact h0.trans (pow_le_pow_left₀ hn hz' 2)
  · refine le_trans ?_ (le_max_left _ _)
    refine (pi_norm_le_iff_of_nonneg (hn.trans hz')).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact (hi i).trans hz'

end RegularityStructures

end
