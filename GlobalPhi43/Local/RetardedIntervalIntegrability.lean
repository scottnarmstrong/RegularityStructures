/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatForcingPotential
public import GlobalPhi43.Local.HeatTimeReflection
public import GlobalPhi43.Local.RetardedChangeVariables

/-! Derive physical-time integrability from actual compact source fields.
The temporary compact bound only licenses integrability, never a PDE norm. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MeasureTheory Real

 theorem retarded_interval_integrable {F : ParabolicSpace → ℝ}
    (hF : Continuous F) (hcF : HasCompactSupport F) {a t : ℝ} (hat : a ≤ t)
    (y : Fin 3 → ℝ) :
    IntervalIntegrable (fun r => ∫ z : Fin 3 → ℝ,
      heatKernelR4 (t - r, y - z) * F (r, z)) volume a t := by
  let φ : ParabolicSpace → ℝ := fun p => F (t - p.1, p.2)
  have hφ : Continuous φ := hF.comp (by fun_prop)
  have hcφ : HasCompactSupport φ := compact_time_reflection hcF t
  obtain ⟨B, hB⟩ := hF.bounded_above_of_compact_support hcF
  let A : ℝ → ℝ := fun s => ∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) * F (t - s, y - w)
  have hI : IntervalIntegrable A volume 0 (t - a) :=
    (heat_forcing_potential_bound hφ hcφ y (sub_nonneg.mpr hat)
      (fun s _ z => by simpa only [φ, Real.norm_eq_abs] using hB (t - s, z))).1
  have heq (r : ℝ) : A (t - r) =
      ∫ z : Fin 3 → ℝ, heatKernelR4 (t - r, y - z) * F (r, z) := by
    have he := integral_sub_left_eq_self
      (fun w : Fin 3 → ℝ => heatKernelR4 (t - r, w) * F (r, y - w)) volume y
    simpa only [A, sub_sub_cancel] using he.symm
  have hrev := hI.comp_sub_left t
  simp only [sub_zero, sub_sub_cancel] at hrev
  apply hrev.symm.congr
  intro r _
  exact heq r

end GlobalPhi43.Local
