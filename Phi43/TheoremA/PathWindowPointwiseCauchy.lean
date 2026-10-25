/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Pointwise Cauchy convergence from compact-window paths

The stopped-limit construction uses pointwise Cauchy sequences, while the stopped-continuity
estimate naturally gives Cauchy convergence in the sup metric on compact time windows.  This module
records the evaluation step between those two formulations.
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assembly_pointwiseCauchy_of_pathWindow
    {Ω : Type*} {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (τ : Ω → ℝ≥0∞)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hwindow : ∀ ω T, 0 ≤ T → ENNReal.ofReal T < τ ω →
      CauchySeq (fun n =>
        ContinuousMap.mk (fun t : Icc (0 : ℝ) T => x n ω t.1)
          (continuousOn_iff_continuous_domRestrict.mp
            ((hcont n ω).mono Icc_subset_Ici_self))))
    {ω : Ω} {t : ℝ} (ht : 0 ≤ t)
    (hτ : ENNReal.ofReal t < τ ω) :
    CauchySeq (fun n => x n ω t) := by
  obtain ⟨T, htT, hTτ⟩ : ∃ T : ℝ, t < T ∧ ENNReal.ofReal T < τ ω := by
    rcases eq_top_or_lt_top (τ ω) with htop | hfinite
    · exact ⟨t + 1, by linarith, by simp [htop]⟩
    · have ht' : t < (τ ω).toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal ht hfinite.ne).mp hτ
      obtain ⟨T, htT, hTτ'⟩ := exists_between ht'
      have hT0 : 0 ≤ T := ht.trans htT.le
      exact ⟨T, htT,
        (ENNReal.ofReal_lt_iff_lt_toReal hT0 hfinite.ne).mpr hTτ'⟩
  have hwindowT := hwindow ω T (ht.trans htT.le) hTτ
  rw [Metric.cauchySeq_iff']
  intro ε hε
  rw [Metric.cauchySeq_iff'] at hwindowT
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := hwindowT (ε / 2) hhalf
  refine ⟨N, fun n hn => ?_⟩
  let a : Icc (0 : ℝ) T := ⟨t, ⟨ht, htT.le⟩⟩
  have hmap : dist
      (ContinuousMap.mk (fun r : Icc (0 : ℝ) T => x n ω r.1)
        (continuousOn_iff_continuous_domRestrict.mp
          ((hcont n ω).mono Icc_subset_Ici_self)))
      (ContinuousMap.mk (fun r : Icc (0 : ℝ) T => x N ω r.1)
        (continuousOn_iff_continuous_domRestrict.mp
        ((hcont N ω).mono Icc_subset_Ici_self))) < ε / 2 :=
    hN n hn
  have hpoint : dist (x n ω t) (x N ω t) ≤ ε / 2 := by
    have hle := (ContinuousMap.dist_le (le_of_lt hhalf)).mp (le_of_lt hmap) a
    change dist (x n ω t) (x N ω t) ≤ ε / 2 at hle
    exact hle
  exact hpoint.trans_lt (by linarith)

end RegularityStructures.Phi43

end
