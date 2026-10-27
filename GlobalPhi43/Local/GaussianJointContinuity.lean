/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatTestGenerator

/-! Continuity and finite time support of the actual joint Gaussian average. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures RegularityStructures.PDE MeasureTheory Filter Topology Real Set

 theorem continuous_gaussian_joint_average {φ : ParabolicSpace → ℝ}
    (hφ : Continuous φ) (hcomp : HasCompactSupport φ) (y : Fin 3 → ℝ) :
    Continuous (fun t : ℝ => ∫ z : Fin 3 → ℝ, gaussKernel 1 z * φ (t, y - √t • z)) := by
  obtain ⟨B, hB⟩ := hφ.bounded_above_of_compact_support hcomp
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z : Fin 3 → ℝ => gaussKernel 1 z * B)
  · exact Eventually.of_forall fun s => (by fun_prop : Continuous _).aestronglyMeasurable
  · apply Eventually.of_forall
    intro s
    apply ae_of_all
    intro z
    rw [norm_mul, Real.norm_of_nonneg (gaussKernel_one_nonneg z)]
    exact mul_le_mul_of_nonneg_left (hB _) (gaussKernel_one_nonneg z)
  · exact integrable_gaussKernel_one.mul_const B
  · apply ae_of_all
    intro z
    exact (show Continuous (fun s : ℝ => gaussKernel 1 z * φ (s, y - √s • z)) by fun_prop).continuousAt.tendsto

 theorem gaussian_joint_average_at_zero (φ : ParabolicSpace → ℝ) (y : Fin 3 → ℝ) :
    (∫ z : Fin 3 → ℝ, gaussKernel 1 z * φ (0, y - √(0 : ℝ) • z)) = φ (0, y) := by
  simp only [Real.sqrt_zero, zero_smul, sub_zero, integral_mul_const,
    integral_gaussKernel (by norm_num : (0 : ℝ) < 1), one_mul]

end GlobalPhi43.Local
