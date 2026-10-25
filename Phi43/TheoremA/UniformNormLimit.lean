/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Uniform bounds from compact-path convergence

Uniform convergence in the continuous-map metric preserves a finite uniform norm bound up to an
arbitrarily small additive margin.  This is the deterministic approximation step used in the
explosion-level argument.
-/

public section

open Filter Topology

namespace RegularityStructures.Phi43

theorem assembly_eventual_uniformNorm_le_of_continuousMap_tendsto
    {η : NegExponent} {T : ℝ}
    (x : ℕ → C(Set.Icc (0 : ℝ) T, HolderBesov η))
    (y : C(Set.Icc (0 : ℝ) T, HolderBesov η))
    (hlim : Tendsto x atTop (𝓝 y))
    {L : ℝ} (hbound : ∀ t : Set.Icc (0 : ℝ) T, ‖y t‖ ≤ L) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : Set.Icc (0 : ℝ) T,
      ‖x n t‖ ≤ L + 1 := by
  have hev : ∀ᶠ n : ℕ in atTop, dist (x n) y < 1 := by
    have hball : Metric.ball y 1 ∈ 𝓝 y := Metric.ball_mem_nhds y zero_lt_one
    have hev' := hlim.eventually hball
    simpa only [Metric.mem_ball] using hev'
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn t => ?_⟩
  have hdist : dist (x n) y < 1 := hN n hn
  have hsub : ‖x n t - y t‖ < 1 := by
    rw [← dist_eq_norm]
    exact (ContinuousMap.dist_apply_le_dist t).trans_lt hdist
  have hsum : ‖x n t‖ < 1 + L := by
    calc
      ‖x n t‖ = ‖(x n t - y t) + y t‖ := by rw [sub_add_cancel]
      _ ≤ ‖x n t - y t‖ + ‖y t‖ := norm_add_le _ _
      _ < 1 + L := add_lt_add_of_lt_of_le hsub (hbound t)
  exact le_of_lt (by linarith only [hsum])

end RegularityStructures.Phi43

end
