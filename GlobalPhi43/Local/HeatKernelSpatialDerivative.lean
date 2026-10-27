/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CompactSpatialSlice
public import RegularityStructures.Analysis.Heat.Kernel

/-! The actual reflected spatial derivative of the ordinary heat kernel. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped ContDiff

 theorem spatial_slice_fderiv_apply {f : ParabolicSpace → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (z v : Fin 3 → ℝ) :
    fderiv ℝ (fun w : Fin 3 → ℝ => f (r, w)) z v = fderiv ℝ f (r, z) (0, v) := by
  rw [spatial_slice_fderiv hf]
  rfl

 theorem spatial_slice_gradient_second {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (r : ℝ) (z v : Fin 3 → ℝ) :
    fderiv ℝ (fun w : Fin 3 → ℝ => fderiv ℝ (fun u : Fin 3 → ℝ => f (r, u)) w v) z v =
      fderiv ℝ (fun q : ParabolicSpace => fderiv ℝ f q (0, v)) (r, z) (0, v) := by
  simp_rw [spatial_slice_fderiv_apply (hf.differentiable (by simp))]
  have hg : ContDiff ℝ ∞ (fun q : ParabolicSpace => fderiv ℝ f q (0, v)) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact spatial_slice_fderiv_apply (hg.differentiable (by simp)) r z v

 theorem heat_kernel_reflected_spatial_derivative {s : ℝ} (hs : 0 < s)
    (y z v : Fin 3 → ℝ) :
    fderiv ℝ (fun w : Fin 3 → ℝ => heatKernelR4 (s, y - w)) z v =
      -fderiv ℝ heatKernelR4 (s, y - z) (0, v) := by
  have hK : DifferentiableAt ℝ heatKernelR4 (s, y - z) :=
    (contDiffAt_heatKernelR4_of_pos hs).differentiableAt (by simp)
  have hmap : HasFDerivAt (fun w : Fin 3 → ℝ => (s, y - w))
      ((0 : (Fin 3 → ℝ) →L[ℝ] ℝ).prod (-(ContinuousLinearMap.id ℝ (Fin 3 → ℝ)))) z :=
    (hasFDerivAt_const s z).prodMk ((hasFDerivAt_id z).const_sub y)
  have hh := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L v) (hK.hasFDerivAt.comp z hmap).fderiv
  change fderiv ℝ (fun w : Fin 3 → ℝ => heatKernelR4 (s, y - w)) z v =
    fderiv ℝ heatKernelR4 (s, y - z) (0, -v) at hh
  rw [show ((0 : ℝ), -v) = -((0 : ℝ), v) by simp, map_neg] at hh
  exact hh

end GlobalPhi43.Local
