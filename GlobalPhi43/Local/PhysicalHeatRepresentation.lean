/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CausalHeatRepresentation
public import Mathlib.MeasureTheory.Group.Integral

/-! Rewrite the genuine causal heat representation in physical source
coordinates. Both substitutions use the actual invariant volume measure. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory
open scoped ContDiff

 theorem physical_heat_representation {u : ParabolicSpace → ℝ}
    (hu : ContDiff ℝ ∞ u) (hcomp : HasCompactSupport u) {a t : ℝ} (hat : a < t)
    (hzero : ∀ z : Fin 3 → ℝ, u (a, z) = 0) (y : Fin 3 → ℝ) :
    (∫ r in a..t, ∫ z : Fin 3 → ℝ,
      heatKernelR4 (t - r, y - z) * sourceHeat u (r, z)) = u (t, y) := by
  have hz : ∀ z : Fin 3 → ℝ, u (t - (t - a), z) = 0 := by simpa only [sub_sub_cancel] using hzero
  have hr := causal_heat_representation_at_time hu hcomp t y (sub_pos.mpr hat) hz
  have hspace (s : ℝ) :
      (∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) * sourceHeat u (t - s, y - w)) =
        ∫ z : Fin 3 → ℝ, heatKernelR4 (s, y - z) * sourceHeat u (t - s, z) := by
    have he := integral_sub_left_eq_self
      (fun w : Fin 3 → ℝ => heatKernelR4 (s, w) * sourceHeat u (t - s, y - w)) volume y
    simpa only [sub_sub_cancel] using he.symm
  simp_rw [hspace] at hr
  let F : ℝ → ℝ := fun r => ∫ z : Fin 3 → ℝ, heatKernelR4 (t - r, y - z) * sourceHeat u (r, z)
  have ht := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t - a) F t
  simp only [F, sub_sub_cancel, sub_zero] at ht
  rw [← ht]
  exact hr

end GlobalPhi43.Local
