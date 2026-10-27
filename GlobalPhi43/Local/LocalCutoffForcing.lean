/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.UnitHeatSource
public import GlobalPhi43.Local.HeatOperatorRegularity
public import GlobalPhi43.Local.HeatForcingPotential
public import GlobalPhi43.Local.HeatTimeReflection

/-! Only the original past-ball PDE supremum enters the forcing estimate.
The qualitative extension is sampled only inside the original carrier. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set Metric Filter Topology MeasureTheory
open scoped ContDiff

 theorem local_cutoff_forcing_potential_bound {χ h g : ParabolicSpace → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hrange : range χ ⊆ Icc 0 1)
    (hs : tsupport χ ⊆ closedBall (0 : ParabolicSpace) (3 / 4 : ℝ))
    (hg : ContDiff ℝ ∞ g) (he : ∀ p ∈ unitHeatPastCarrier, g =ᶠ[𝓝 p] h)
    {F t T : ℝ} (hF : 0 ≤ F) (ht : t ≤ 0) (hT : 0 ≤ T)
    (hPDE : ∀ p ∈ pastBall (0 : ParabolicSpace) 1, |sourceHeat h p| ≤ F)
    (y : Fin 3 → ℝ) :
    IntervalIntegrable (fun s => ∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) *
      (χ (t - s, y - w) * sourceHeat g (t - s, y - w))) volume 0 T ∧
    |∫ s in (0 : ℝ)..T, ∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) *
      (χ (t - s, y - w) * sourceHeat g (t - s, y - w))| ≤ T * F := by
  let φ : ParabolicSpace → ℝ := fun p => χ (t - p.1, p.2) * sourceHeat g (t - p.1, p.2)
  have hφ : ContDiff ℝ ∞ φ := (hχ.mul (sourceHeat_contDiff hg)).comp (by fun_prop)
  have hcφ : HasCompactSupport φ := compact_time_reflection hcχ.mul_right t
  apply heat_forcing_potential_bound hφ.continuous hcφ y hT
  intro s hstime z
  change |χ (t - s, z) * sourceHeat g (t - s, z)| ≤ F
  by_cases hz : χ (t - s, z) = 0
  · simpa only [hz, zero_mul, abs_zero] using hF
  · have hqnorm : ‖((t - s, z) : ParabolicSpace)‖ ≤ 3 / 4 := by
      simpa only [mem_closedBall, dist_zero_right] using hs (subset_tsupport χ hz)
    have hq : ((t - s, z) : ParabolicSpace) ∈ unitHeatSourceDomain := by
      constructor
      · rw [mem_ball, dist_zero_right]
        linarith
      · change t - s < 0
        linarith [hstime.1]
    have hLg := sourceHeat_eq_of_eventuallyEq (he _ (unitHeatSourceDomain_subset_carrier hq))
    have hLf := hPDE _ (unitHeatSourceDomain_subset_pastBall hq)
    have hχq := hrange ⟨(t - s, z), rfl⟩
    rw [abs_mul, abs_of_nonneg hχq.1, hLg]
    calc
      χ (t - s, z) * |sourceHeat h (t - s, z)| ≤ 1 * F :=
        mul_le_mul hχq.2 hLf (abs_nonneg _) (by norm_num)
      _ = F := one_mul _

end GlobalPhi43.Local
