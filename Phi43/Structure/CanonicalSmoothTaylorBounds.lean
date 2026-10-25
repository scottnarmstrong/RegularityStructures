/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TaylorKernel.ProfileDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import RegularityStructures.Abstract.Singular.Remainder.TaylorQuant
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Local parabolic Taylor bounds for smooth functions

The smooth-function Taylor estimate used for the canonical structure-group
bounds [Hai14, Proposition 8.27]. A compact cutoff permits applying the
analysis layer's Taylor profile estimate without any temporal growth condition.
-/

public noncomputable section

open Set

namespace RegularityStructures.Phi43

open scoped ContDiff in
/-- The parabolic Taylor remainder of a smooth function has the expected
order locally uniformly in the base point. -/
theorem canonicalSmooth_compact_taylor_bound {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) {S : Set ParabolicSpace} (hS : IsCompact S)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ v : ParabolicSpace,
      parabolicNorm v ≤ 1 → |taylorProfile f σ v x| ≤ C * parabolicNorm v ^ σ := by
  obtain ⟨R, hR0, hR⟩ := hS.isBounded.subset_closedBall_lt 0 (0 : ParabolicSpace)
  obtain ⟨χ, hχ, _, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (s := Metric.ball (0 : ParabolicSpace) (R + 3))
    (t := Metric.closedBall (0 : ParabolicSpace) (R + 2))
    Metric.isOpen_ball Metric.isClosed_closedBall
    (Metric.closedBall_subset_ball (by linarith))
  have hχc : HasCompactSupport χ := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ParabolicSpace) (R + 3))
    intro y hy
    have hnot : y ∉ Function.support χ := by
      rw [hsupp]
      exact fun h => hy (Metric.ball_subset_closedBall h)
    exact not_not.1 hnot
  let F : ParabolicSpace → ℝ := fun y => χ y * f y
  have hF : ContDiff ℝ ∞ F := hχ.mul hf
  have hFc : HasCompactSupport F := hχc.mul_right
  have heq (y : ParabolicSpace) (hy : y ∈ Metric.ball (0 : ParabolicSpace) (R + 2)) :
      F y = f y := by
    change χ y * f y = f y
    rw [(hone y).1 (Metric.ball_subset_closedBall hy), one_mul]
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedFDeriv_taylorProfile_le hF hFc hσ
  refine ⟨C, hC0, fun x hx v hv => ?_⟩
  have hxR : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hR hx
  have hxU : x ∈ Metric.ball (0 : ParabolicSpace) (R + 2) := by
    simpa only [Metric.mem_ball, dist_zero_right] using (show ‖x‖ < R + 2 by linarith)
  have hxvU : x + v ∈ Metric.ball (0 : ParabolicSpace) (R + 2) := by
    have hvn := norm_le_one_of_parabolicNorm_le_one hv
    have hh := norm_add_le x v
    simpa only [Metric.mem_ball, dist_zero_right] using
      (show ‖x + v‖ < R + 2 by linarith)
  have he : taylorProfile F σ v x = taylorProfile f σ v x := by
    unfold taylorProfile
    rw [heq _ hxvU]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [lineIter_congr_of_isOpen Metric.isOpen_ball heq (multiDirs k) x hxU]
  have hh := hC v hv 0 (by norm_num) x
  simpa only [iteratedFDeriv_zero_apply, norm_iteratedFDeriv_zero, Real.norm_eq_abs, he] using hh

end RegularityStructures.Phi43

end
