/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatTimeReflection
public import GlobalPhi43.Local.HeatKernelFundamentalIdentity

/-! Causal ordinary-heat representation of an actual compact smooth field. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory
open scoped ContDiff

/-- A preselected lower time slice at which the entire field vanishes gives
the exact causal heat representation, with the actual source heat operator. -/
theorem causal_heat_representation_at_time {u : ParabolicSpace → ℝ}
    (hu : ContDiff ℝ ∞ u) (hcomp : HasCompactSupport u) (t₀ : ℝ) (y : Fin 3 → ℝ)
    {T : ℝ} (hT : 0 < T) (hzero : ∀ w : Fin 3 → ℝ, u (t₀ - T, w) = 0) :
    (∫ s in (0 : ℝ)..T, ∫ w : Fin 3 → ℝ,
      heatKernelR4 (s, w) * sourceHeat u (t₀ - s, y - w)) = u (t₀, y) := by
  let φ : ParabolicSpace → ℝ := fun p => u (t₀ - p.1, p.2)
  have hφ : ContDiff ℝ ∞ φ := hu.comp (by fun_prop)
  have hcφ : HasCompactSupport φ := compact_time_reflection hcomp t₀
  have hid := heatKernel_fundamental_identity_at_time hφ hcφ y hT hzero
  have he (s : ℝ) (w : Fin 3 → ℝ) : -heatTestGenerator φ (s, y - w) =
      sourceHeat u (t₀ - s, y - w) := by
    rw [heatTestGenerator_time_reflection hu, neg_neg]
  simp_rw [he] at hid
  simpa only [φ, sub_zero] using hid

end GlobalPhi43.Local
