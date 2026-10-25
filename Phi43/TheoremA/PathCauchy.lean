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
# Uniform Cauchy extraction

This is the metric step used after the stopped-continuity estimate for classical solutions has been
specialised to a fixed sample and horizon.  It keeps the model distance abstract, so the analytic
argument is not coupled to the representation of `phi43Dist`.
-/

public section

open Set Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assembly_path_cauchy_of_steps
    {η : NegExponent} {T : ℝ} (hT : 0 ≤ T)
    (x : ℕ → ℝ → HolderBesov η)
    (hcont : ∀ n, ContinuousOn (x n) (Ici (0 : ℝ)))
    (d : ℕ → ℕ → ℝ≥0∞)
    (hmetric : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      d n m ≤ ENNReal.ofReal δ)
    (hbound : ∃ L : ℝ, ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T, ‖x n t‖ ≤ L)
    (hstab : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n m : ℕ, d n m ≤ ENNReal.ofReal δ →
        (∀ t ∈ Icc (0 : ℝ) T, ‖x n t‖ ≤ Classical.choose hbound ∧
          ‖x m t‖ ≤ Classical.choose hbound) →
        ∀ t ∈ Icc (0 : ℝ) T, dist (x n t) (x m t) ≤ ε) :
    CauchySeq (fun n =>
      ContinuousMap.mk (fun t : Icc (0 : ℝ) T => x n t.1)
        (continuousOn_iff_continuous_domRestrict.mp
          ((hcont n).mono Icc_subset_Ici_self))) := by
  let L : ℝ := Classical.choose hbound
  have hL : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T, ‖x n t‖ ≤ L :=
    Classical.choose_spec hbound
  have hstab' : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n m : ℕ, d n m ≤ ENNReal.ofReal δ →
        (∀ t ∈ Icc (0 : ℝ) T, ‖x n t‖ ≤ L ∧ ‖x m t‖ ≤ L) →
        ∀ t ∈ Icc (0 : ℝ) T, dist (x n t) (x m t) ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hstab ε hε
    refine ⟨δ, hδ, ?_⟩
    intro n m hnm hb
    apply h n m hnm
    exact hb
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨δ, hδ, hδstab⟩ := hstab' (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := hmetric δ hδ
  refine ⟨N, fun n hn => ?_⟩
  let _ : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  rw [ContinuousMap.dist_eq_iSup]
  have hhalf : ε / 2 < ε := by linarith only [hε]
  apply lt_of_le_of_lt ?_ hhalf
  apply ciSup_le
  intro t
  have hpoint := hδstab n N (hN n N hn le_rfl) (fun s hs =>
    ⟨hL n s hs, hL N s hs⟩) t.1 t.2
  exact hpoint

end RegularityStructures.Phi43

end
