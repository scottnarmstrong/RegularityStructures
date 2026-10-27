/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatBoundaryFamily
public import RegularityStructures.Analysis.Heat.Kernel

/-! Classical spatial regularity of the actual positive-time kernel family. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped ContDiff

 theorem positive_heat_boundary_kernel_contDiff {s : ℝ} (hs : 0 < s)
    (y : Fin 3 → ℝ) (i : Option (Fin 3)) :
    ContDiff ℝ ∞ (fun z : Fin 3 → ℝ => heatBoundaryKernel heatKernelR4 i (s, y - z)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have hK : ContDiffAt ℝ ∞ heatKernelR4 (s, y - z) := contDiffAt_heatKernelR4_of_pos hs
  have hKi : ContDiffAt ℝ ∞ (heatBoundaryKernel heatKernelR4 i) (s, y - z) := by
    cases i with
    | none => exact hK
    | some j => exact (hK.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  exact hKi.comp (f := fun w : Fin 3 → ℝ => (s, y - w)) z (by fun_prop)

end GlobalPhi43.Local
