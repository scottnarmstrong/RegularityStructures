/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SpatialCutoffPairing
public import GlobalPhi43.Local.HeatKernelSpatialDerivative
public import GlobalPhi43.Local.PositiveHeatBoundaryKernel
public import GlobalPhi43.Local.HeatOperatorRegularity
public import GlobalPhi43.Local.HeatProductRule

/-! The actual positive-time spatial cutoff identity: forcing plus the
four boundary terms, with every integrability obligation discharged. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory
open scoped ContDiff

 theorem spatial_heat_cutoff_identity {χ g : ParabolicSpace → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hg : ContDiff ℝ ∞ g)
    {r t : ℝ} (hrt : r < t) (y : Fin 3 → ℝ) :
    (∫ z : Fin 3 → ℝ, heatKernelR4 (t - r, y - z) * sourceHeat (fun q => χ q * g q) (r, z)) =
      (∫ z : Fin 3 → ℝ, heatKernelR4 (t - r, y - z) * (χ (r, z) * sourceHeat g (r, z))) +
      ∑ i : Option (Fin 3), ∫ z : Fin 3 → ℝ, heatBoundaryKernel heatKernelR4 i (t - r, y - z) *
        (heatBoundaryCoefficient χ i (r, z) * g (r, z)) := by
  have hs : 0 < t - r := sub_pos.mpr hrt
  have hk : ContDiff ℝ ∞ (fun z : Fin 3 → ℝ => heatKernelR4 (t - r, y - z)) :=
    positive_heat_boundary_kernel_contDiff hs y none
  have hsliceχ := smooth_spatial_slice hχ r
  have hsliceg := smooth_spatial_slice hg r
  have hsliceb := smooth_spatial_slice (sourceHeat_contDiff hχ) r
  have hcχslice := compact_spatial_slice hcχ r
  have hcbslice := compact_spatial_slice (sourceHeat_hasCompactSupport hcχ) r
  have hpair := spatial_cutoff_pairing hk hsliceχ hsliceg hsliceb hcχslice hcbslice
  simp_rw [spatial_slice_gradient_second hχ r,
    spatial_slice_fderiv_apply (hχ.differentiable (by simp)) r,
    spatial_slice_fderiv_apply (hg.differentiable (by simp)) r,
    heat_kernel_reflected_spatial_derivative hs y] at hpair
  have htrace (z : Fin 3 → ℝ) : sourceHeat χ (r, z) + 2 * ∑ i : Fin 3,
      fderiv ℝ (fun q : ParabolicSpace => fderiv ℝ χ q (0, Pi.single i 1)) (r, z) (0, Pi.single i 1) =
        heatTestGenerator χ (r, z) := by
    rw [sourceHeat_eq_testGenerator hχ]
    unfold heatTestGenerator
    ring
  simp_rw [htrace] at hpair
  have hforceC : ContDiff ℝ ∞ (fun q => χ q * sourceHeat g q) := hχ.mul (sourceHeat_contDiff hg)
  have hforceHC : HasCompactSupport (fun q => χ q * sourceHeat g q) := hcχ.mul_right
  have hforceSlice := smooth_spatial_slice hforceC r
  have hiF : Integrable (fun z : Fin 3 → ℝ => heatKernelR4 (t - r, y - z) *
      (χ (r, z) * sourceHeat g (r, z))) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (compact_spatial_slice hforceHC r).mul_left
  have hKC (i : Option (Fin 3)) := positive_heat_boundary_kernel_contDiff hs y i
  have hAC (i : Option (Fin 3)) := smooth_spatial_slice (heatBoundaryCoefficient_contDiff hχ i) r
  have hcA (i : Option (Fin 3)) := compact_spatial_slice (heatBoundaryCoefficient_hasCompactSupport hcχ i) r
  have hiB (i : Option (Fin 3)) : Integrable (fun z : Fin 3 → ℝ => heatBoundaryKernel heatKernelR4 i (t - r, y - z) *
      (heatBoundaryCoefficient χ i (r, z) * g (r, z))) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (hcA i).mul_right.mul_left
  have hopt (z : Fin 3 → ℝ) :
      (heatKernelR4 (t - r, y - z) * heatTestGenerator χ (r, z) +
        2 * ∑ i : Fin 3, (-fderiv ℝ heatKernelR4 (t - r, y - z) (0, Pi.single i 1)) *
          fderiv ℝ χ (r, z) (0, Pi.single i 1)) * g (r, z) =
      ∑ i : Option (Fin 3), heatBoundaryKernel heatKernelR4 i (t - r, y - z) *
        (heatBoundaryCoefficient χ i (r, z) * g (r, z)) := by
    rw [Fintype.sum_option]
    simp only [heatBoundaryKernel, heatBoundaryCoefficient]
    have hneg : (∑ i : Fin 3, (-fderiv ℝ heatKernelR4 (t - r, y - z) (0, Pi.single i 1)) *
        fderiv ℝ χ (r, z) (0, Pi.single i 1)) =
      -(∑ i : Fin 3, fderiv ℝ heatKernelR4 (t - r, y - z) (0, Pi.single i 1) *
        fderiv ℝ χ (r, z) (0, Pi.single i 1)) := by simp only [neg_mul, Finset.sum_neg_distrib]
    have hscaled : (∑ i : Fin 3, fderiv ℝ heatKernelR4 (t - r, y - z) (0, Pi.single i 1) *
        ((-2 : ℝ) * fderiv ℝ χ (r, z) (0, Pi.single i 1) * g (r, z))) =
      (-2 : ℝ) * (∑ i : Fin 3, fderiv ℝ heatKernelR4 (t - r, y - z) (0, Pi.single i 1) *
        fderiv ℝ χ (r, z) (0, Pi.single i 1)) * g (r, z) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg, hscaled]
    ring
  have heq : (fun z : Fin 3 → ℝ => heatKernelR4 (t - r, y - z) * sourceHeat (fun q => χ q * g q) (r, z)) =
      (fun z => heatKernelR4 (t - r, y - z) * (χ (r, z) * sourceHeat g (r, z)) +
        heatKernelR4 (t - r, y - z) * (g (r, z) * sourceHeat χ (r, z) - 2 * ∑ i : Fin 3,
          fderiv ℝ χ (r, z) (0, Pi.single i 1) * fderiv ℝ g (r, z) (0, Pi.single i 1))) := by
    funext z
    rw [sourceHeat_product hχ hg]
    ring
  rw [heq, integral_add hiF hpair.1, hpair.2]
  congr 1
  rw [← integral_finsetSum Finset.univ (fun i _ => hiB i)]
  apply integral_congr_ae
  exact ae_of_all _ hopt

end GlobalPhi43.Local
