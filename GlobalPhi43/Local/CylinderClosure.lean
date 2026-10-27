/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CompactCylinderSup
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! The exact closed carrier of the local smoothness hypothesis. -/
public section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20
open scoped ContDiff

/-- The source cylinder is a time interval times the spatial sup-norm unit ball. -/
theorem sourceCylinder_zero_eq_prod :
    sourceCylinder 0 = Ioo (0 : ℝ) 1 ×ˢ Metric.ball (0 : Fin 3 → ℝ) 1 := by
  ext z
  change ((0 : ℝ) ^ 2 < z.1 ∧ z.1 < 1 ∧ ∀ i, |z.2 i| < 1 - 0) ↔
    (0 < z.1 ∧ z.1 < 1) ∧ dist z.2 0 < 1
  rw [dist_zero_right, pi_norm_lt_iff (by norm_num)]
  simp only [Real.norm_eq_abs, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
  tauto

/-- Closing P gives precisely the closed cylinder used by the source supremum. -/
theorem closure_sourceCylinder_zero : closure (sourceCylinder 0) = sourceClosedCylinder := by
  rw [sourceCylinder_zero_eq_prod, closure_prod_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
    closure_ball (0 : Fin 3 → ℝ) (by norm_num : (1 : ℝ) ≠ 0)]
  ext z
  change ((0 ≤ z.1 ∧ z.1 ≤ 1) ∧ dist z.2 0 ≤ 1) ↔
    ((0 ≤ z.1 ∧ (fun _ => (-1 : ℝ)) ≤ z.2) ∧
      (z.1 ≤ 1 ∧ z.2 ≤ fun _ => (1 : ℝ)))
  rw [dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
  simp only [Real.norm_eq_abs, abs_le, Pi.le_def]
  constructor
  · rintro ⟨⟨ht₀, ht₁⟩, hx⟩
    exact ⟨⟨ht₀, fun i => (hx i).1⟩, ⟨ht₁, fun i => (hx i).2⟩⟩
  · rintro ⟨⟨ht₀, hx₀⟩, ⟨ht₁, hx₁⟩⟩
    exact ⟨⟨ht₀, ht₁⟩, fun i => ⟨hx₀ i, hx₁ i⟩⟩

/-- Local smoothness of u and continuity of J on the closed carrier are enough
for all cylinder supremum arguments applied to v=u-J. -/
theorem remainder_continuousOn_closed (u J : ParabolicSpace → ℝ)
    (hu : ∃ O : Set ParabolicSpace, IsOpen O ∧ closure (sourceCylinder 0) ⊆ O ∧
      ContDiffOn ℝ ∞ u O) (hJ : ContinuousOn J sourceClosedCylinder) :
    ContinuousOn (fun z => u z - J z) sourceClosedCylinder := by
  obtain ⟨O, _, hO, huO⟩ := hu
  rw [closure_sourceCylinder_zero] at hO
  exact (huO.continuousOn.mono hO).sub hJ

end GlobalPhi43.Local
