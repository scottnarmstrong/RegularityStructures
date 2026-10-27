/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SpatialHeatCutoffIdentity
public import GlobalPhi43.Local.BoundaryPotentialTimeIntegral
public import GlobalPhi43.Local.RetardedIntervalIntegrability

/-! The exact local unit cutoff formula: actual forcing potential plus
actual boundary potential, with no representation premise. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set Metric Filter Topology MeasureTheory
open scoped ContDiff

 theorem unit_cutoff_heat_representation {χ g : ParabolicSpace → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hg : ContDiff ℝ ∞ g)
    (hs : tsupport χ ⊆ closedBall (0 : ParabolicSpace) (3 / 4 : ℝ))
    (hone : ∀ p ∈ closedBall (0 : ParabolicSpace) (1 / 2 : ℝ), χ p = 1)
    {p : ParabolicSpace} (hp : ‖p‖ ≤ 1 / 4) (ht : p.1 ≤ 0) :
    (∫ s in (0 : ℝ)..(p.1 + 1), ∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) *
      (χ (p.1 - s, p.2 - w) * sourceHeat g (p.1 - s, p.2 - w))) +
        heatBoundaryPotential heatKernelR4 χ unitHeatSourceMeasure g p = g p := by
  have hlow := unit_core_time_lower hp
  have hzero (z : Fin 3 → ℝ) : χ (-1, z) * g (-1, z) = 0 := by
    rw [fixed_cutoff_lower_slice_zero hs, zero_mul]
  have hrepr := physical_heat_representation (hχ.mul hg) hcχ.mul_right hlow hzero p.2
  simp only [Prod.mk.eta] at hrepr
  rw [fixed_cutoff_core_one hone hp, one_mul] at hrepr
  obtain ⟨k, hk, _, he, _⟩ := exists_fixed_annular_heat_kernel
  have hboundary := boundary_potential_time_integral hχ hcχ hk hg.continuous hs hone he hp ht
  have hforceC : ContDiff ℝ ∞ (fun q => χ q * sourceHeat g q) := hχ.mul (sourceHeat_contDiff hg)
  have hforceHC : HasCompactSupport (fun q => χ q * sourceHeat g q) := hcχ.mul_right
  have hiForce := retarded_interval_integrable hforceC.continuous hforceHC hlow.le p.2
  have hiBoundary : IntervalIntegrable (fun r => ∑ i : Option (Fin 3), ∫ z : Fin 3 → ℝ,
      heatBoundaryKernel heatKernelR4 i (p - (r, z)) *
        (heatBoundaryCoefficient χ i (r, z) * g (r, z))) volume (-1) p.1 := by
    constructor
    · exact integrable_finsetSum Finset.univ (fun i _ => (hboundary.1 i).1)
    · exact integrable_finsetSum Finset.univ (fun i _ => (hboundary.1 i).2)
  have hpoint (r : ℝ) (z : Fin 3 → ℝ) : p - (r, z) = (p.1 - r, p.2 - z) := by
    apply Prod.ext <;> rfl
  have hdecomp : (∫ r in (-1 : ℝ)..p.1, ∫ z : Fin 3 → ℝ,
      heatKernelR4 (p.1 - r, p.2 - z) * sourceHeat (fun q => χ q * g q) (r, z)) =
    (∫ r in (-1 : ℝ)..p.1, (∫ z : Fin 3 → ℝ, heatKernelR4 (p.1 - r, p.2 - z) *
      (χ (r, z) * sourceHeat g (r, z))) + ∑ i : Option (Fin 3), ∫ z : Fin 3 → ℝ,
        heatBoundaryKernel heatKernelR4 i (p - (r, z)) *
          (heatBoundaryCoefficient χ i (r, z) * g (r, z))) := by
    apply intervalIntegral.integral_congr_uIoo
    intro r hr
    rw [uIoo_of_le hlow.le] at hr
    simpa only [hpoint] using spatial_heat_cutoff_identity hχ hcχ hg hr.2 p.2
  rw [intervalIntegral.integral_add hiForce hiBoundary, ← hboundary.2] at hdecomp
  have htransform := retarded_heat_integral_change_variables (fun q => χ q * sourceHeat g q) (-1) p.1 p.2
  simp only [sub_neg_eq_add] at htransform
  rw [htransform] at hdecomp
  exact hdecomp.symm.trans hrepr

end GlobalPhi43.Local
