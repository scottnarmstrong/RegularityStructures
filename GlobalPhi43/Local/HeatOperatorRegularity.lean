/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatOperatorSlices
public import GlobalPhi43.Local.HeatGermLocality

/-! Regularity and compact support of the literal coordinate heat operator. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Filter Topology
open scoped ContDiff

 theorem sourceHeat_eq_testGenerator {u : ParabolicSpace → ℝ} (hu : ContDiff ℝ ∞ u) :
    sourceHeat u = fun p => 2 * fderiv ℝ u p (1, 0) - heatTestGenerator u p := by
  funext p
  rw [sourceHeat_eq_fderiv_of_contDiffAt u p (hu.contDiffAt.of_le (by norm_num))]
  unfold heatTestGenerator
  simp_rw [coordinate_second_fderiv hu]
  ring

 theorem sourceHeat_contDiff {u : ParabolicSpace → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (sourceHeat u) := by
  rw [sourceHeat_eq_testGenerator hu]
  have ht : ContDiff ℝ ∞ (fun p : ParabolicSpace => fderiv ℝ u p (1, 0)) :=
    (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact (contDiff_const.mul ht).sub (heatTestGenerator_contDiff hu)

 theorem sourceHeat_hasCompactSupport {u : ParabolicSpace → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (sourceHeat u) := by
  apply hu.mono'
  intro p hp
  by_contra hps
  have he : u =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hps] with q hq
    exact image_eq_zero_of_notMem_tsupport hq
  have hz : sourceHeat u p = 0 := by
    rw [sourceHeat_eq_of_eventuallyEq he]
    simp [sourceHeat]
  exact hp hz

end GlobalPhi43.Local
