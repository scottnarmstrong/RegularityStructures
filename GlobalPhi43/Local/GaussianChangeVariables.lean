/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RegularityStructures.PDE.HeatOpBridge
public import RegularityStructures.Analysis.Heat.Kernel
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact Euclidean Gaussian scaling, reusing the pinned Jacobian formula. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures RegularityStructures.PDE MeasureTheory Real

 theorem gaussian_change_variables {t : ℝ} (ht : 0 < t) (f : (Fin 3 → ℝ) → ℝ) :
    (∫ z : Fin 3 → ℝ, gaussKernel 1 z * f (√t • z)) =
      ∫ w : Fin 3 → ℝ, heatKernelR4 (t, w) * f w := by
  let F : (Fin 3 → ℝ) → ℝ := fun w => gaussKernel t w * f w
  have h1 : (∫ z : Fin 3 → ℝ, gaussKernel 1 z * f (√t • z)) =
      √t ^ 3 * ∫ z : Fin 3 → ℝ, F (√t • z) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    dsimp only [F]
    rw [gaussKernel_one_eq ht z]
    ring
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  rw [h1, Measure.integral_comp_smul, Module.finrank_fin_fun, smul_eq_mul, ← mul_assoc,
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), one_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  simp [F, heatKernelR4, ht]

end GlobalPhi43.Local
