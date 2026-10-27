/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.BoundaryTimeSupport
public import GlobalPhi43.Local.CompactSourceTimeIntegral

/-! Attach the actual boundary potential to physical retarded time integrals.
All Fubini and interval-integrability obligations are derived from support. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric Filter Topology MeasureTheory
open scoped ContDiff

 theorem boundary_potential_time_integral {χ k g : ParabolicSpace → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hk : ContDiff ℝ ∞ k)
    (hg : Continuous g) (hs : tsupport χ ⊆ closedBall (0 : ParabolicSpace) (3 / 4 : ℝ))
    (hone : ∀ p ∈ closedBall (0 : ParabolicSpace) (1 / 2 : ℝ), χ p = 1)
    (he : ∀ z ∈ fixedHeatAnnulus, k =ᶠ[𝓝 z] heatKernelR4)
    {p : ParabolicSpace} (hp : ‖p‖ ≤ 1 / 4) (ht : p.1 ≤ 0) :
    (∀ i : Option (Fin 3), IntervalIntegrable
      (fun r => ∫ z : Fin 3 → ℝ, heatBoundaryKernel heatKernelR4 i (p - (r, z)) *
        (heatBoundaryCoefficient χ i (r, z) * g (r, z))) volume (-1) p.1) ∧
    heatBoundaryPotential heatKernelR4 χ unitHeatSourceMeasure g p =
      ∫ r in (-1 : ℝ)..p.1, ∑ i : Option (Fin 3), ∫ z : Fin 3 → ℝ,
        heatBoundaryKernel heatKernelR4 i (p - (r, z)) *
          (heatBoundaryCoefficient χ i (r, z) * g (r, z)) := by
  let F : Option (Fin 3) → ParabolicSpace → ℝ := fun i q =>
    heatBoundaryKernel k i (p - q) * (heatBoundaryCoefficient χ i q * g q)
  have hK (i : Option (Fin 3)) : Continuous (heatBoundaryKernel k i) :=
    (heatBoundaryKernel_contDiff hk i).continuous
  have hA (i : Option (Fin 3)) : Continuous (heatBoundaryCoefficient χ i) :=
    (heatBoundaryCoefficient_contDiff hχ i).continuous
  have hcA (i : Option (Fin 3)) : HasCompactSupport (heatBoundaryCoefficient χ i) :=
    heatBoundaryCoefficient_hasCompactSupport hcχ i
  have hFC (i : Option (Fin 3)) : Continuous (F i) := by dsimp only [F]; fun_prop
  have hcF (i : Option (Fin 3)) : HasCompactSupport (F i) := (hcA i).mul_right.mul_left
  have htime (i : Option (Fin 3)) := compact_source_time_integral (hFC i) (hcF i)
    (unit_core_time_lower hp).le
    (fun q hq => boundary_integrand_zero_off_unit_domain hs hone he hp ht hq i (g q))
    (fun r hr z => boundary_integrand_zero_off_time hs hone he hp ht hr i (g (r, z)))
  have hspace (i : Option (Fin 3)) (r : ℝ) : (∫ z : Fin 3 → ℝ, F i (r, z)) =
      ∫ z : Fin 3 → ℝ, heatBoundaryKernel heatKernelR4 i (p - (r, z)) *
        (heatBoundaryCoefficient χ i (r, z) * g (r, z)) := by
    apply integral_congr_ae
    apply ae_of_all
    intro z
    dsimp only [F]
    by_cases hz : heatBoundaryCoefficient χ i (r, z) = 0
    · simp only [hz, zero_mul, mul_zero]
    · rw [boundary_kernel_agreement hs hone he hp i hz]
  have hactual (i : Option (Fin 3)) : Integrable
      (fun r => ∫ z : Fin 3 → ℝ, heatBoundaryKernel heatKernelR4 i (p - (r, z)) *
        (heatBoundaryCoefficient χ i (r, z) * g (r, z))) :=
    (htime i).1.congr (ae_of_all _ (hspace i))
  have heq (i : Option (Fin 3)) : (∫ q, F i q ∂unitHeatSourceMeasure) =
      ∫ r in (-1 : ℝ)..p.1, ∫ z : Fin 3 → ℝ, heatBoundaryKernel heatKernelR4 i (p - (r, z)) *
        (heatBoundaryCoefficient χ i (r, z) * g (r, z)) := by
    apply (htime i).2.trans
    apply intervalIntegral.integral_congr_ae
    exact ae_of_all _ fun r _ => hspace i r
  refine ⟨fun i => (hactual i).intervalIntegrable, ?_⟩
  rw [← heatBoundaryPotential_agreement hs hone he unitHeatSourceMeasure g hp]
  change (∑ i : Option (Fin 3), ∫ q, F i q ∂unitHeatSourceMeasure) = _
  simp_rw [heq]
  exact (intervalIntegral.integral_finsetSum (fun i _ => (hactual i).intervalIntegrable)).symm

end GlobalPhi43.Local
