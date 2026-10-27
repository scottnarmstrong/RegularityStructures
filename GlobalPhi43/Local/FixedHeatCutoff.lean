/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CompactSmoothExtension
public import GlobalPhi43.Local.HeatGermLocality
public import Mathlib.Tactic

/-! One fixed unit-box heat cutoff, selected before any field or data. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set Metric Filter Topology
open scoped ContDiff

 theorem exists_fixed_heat_cutoff : ∃ χ : ParabolicSpace → ℝ,
    ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ range χ ⊆ Icc 0 1 ∧
    tsupport χ ⊆ closedBall 0 (3 / 4 : ℝ) ∧
    (∀ p ∈ closedBall 0 (1 / 2 : ℝ), χ p = 1) := by
  obtain ⟨χ, hχ, hrange, hsχ, hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (s := ball (0 : ParabolicSpace) (3 / 4 : ℝ))
    (t := closedBall (0 : ParabolicSpace) (1 / 2 : ℝ)) isOpen_ball isClosed_closedBall
    (closedBall_subset_ball (by norm_num))
  have ht : tsupport χ ⊆ closedBall 0 (3 / 4 : ℝ) := by
    apply closure_minimal _ isClosed_closedBall
    rw [hsχ]
    exact ball_subset_closedBall
  have hc : HasCompactSupport χ :=
    (isCompact_closedBall (0 : ParabolicSpace) (3 / 4 : ℝ)).of_isClosed_subset (isClosed_tsupport χ) ht
  exact ⟨χ, hχ, hc, hrange, ht, fun p hp => (hone p).1 hp⟩

/-- Every first or second differential cutoff term vanishes in the open
inner box, by germ locality, without differentiating an indicator. -/
theorem fixed_cutoff_inner_germ {χ : ParabolicSpace → ℝ}
    (hone : ∀ p ∈ closedBall (0 : ParabolicSpace) (1 / 2 : ℝ), χ p = 1)
    {p : ParabolicSpace} (hp : p ∈ ball 0 (1 / 2 : ℝ)) :
    χ =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
  filter_upwards [isOpen_ball.mem_nhds hp] with q hq
  exact hone q (ball_subset_closedBall hq)

end GlobalPhi43.Local
