/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatTestGenerator
public import GlobalPhi43.MW20.HeatFrechet

/-! Attach the compact-test generator to the actual coordinate heat operator. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20
open scoped ContDiff

 theorem coordinate_second_fderiv {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (p v w : ParabolicSpace) :
    fderiv ℝ (fun q => fderiv ℝ φ q w) p v = fderiv ℝ (fderiv ℝ φ) p v w := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hh := congrArg (fun L : ParabolicSpace →L[ℝ] ℝ => L v)
    (((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp p
      (hd.differentiable (by simp) p).hasFDerivAt).fderiv)
  exact hh

 theorem spatial_slice_second_joint {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (t : ℝ) (w v₁ v₂ : Fin 3 → ℝ) :
    fderiv ℝ (fderiv ℝ (fun z : Fin 3 → ℝ => φ (t, z))) w v₁ v₂ =
      fderiv ℝ (fderiv ℝ φ) (t, w) (0, v₁) (0, v₂) := by
  rw [spatial_slice_second_apply hφ, coordinate_second_fderiv hφ]

 theorem sourceHeat_eq_spatial_slices {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (p : ParabolicSpace) :
    sourceHeat φ p = fderiv ℝ φ p (1, 0) - ∑ i : Fin 3,
      fderiv ℝ (fderiv ℝ (fun w : Fin 3 → ℝ => φ (p.1, w))) p.2 (Pi.single i 1) (Pi.single i 1) := by
  rw [sourceHeat_eq_fderiv_of_contDiffAt φ p (hφ.contDiffAt.of_le (by norm_num))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (spatial_slice_second_joint hφ p.1 p.2 (Pi.single i 1) (Pi.single i 1)).symm

end GlobalPhi43.Local
