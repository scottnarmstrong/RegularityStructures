/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.PhysicalHeatRepresentation

/-! Exact retarded source-coordinate substitution for every source field. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MeasureTheory

 theorem retarded_heat_integral_change_variables (F : ParabolicSpace → ℝ) (a t : ℝ) (y : Fin 3 → ℝ) :
    (∫ r in a..t, ∫ z : Fin 3 → ℝ, heatKernelR4 (t - r, y - z) * F (r, z)) =
      ∫ s in (0 : ℝ)..(t - a), ∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) * F (t - s, y - w) := by
  have hspace (s : ℝ) :
      (∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) * F (t - s, y - w)) =
        ∫ z : Fin 3 → ℝ, heatKernelR4 (s, y - z) * F (t - s, z) := by
    have he := integral_sub_left_eq_self
      (fun w : Fin 3 → ℝ => heatKernelR4 (s, w) * F (t - s, y - w)) volume y
    simpa only [sub_sub_cancel] using he.symm
  simp_rw [hspace]
  let B : ℝ → ℝ := fun r => ∫ z : Fin 3 → ℝ, heatKernelR4 (t - r, y - z) * F (r, z)
  have he := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t - a) B t
  simpa only [B, sub_sub_cancel, sub_zero] using he.symm

end GlobalPhi43.Local
