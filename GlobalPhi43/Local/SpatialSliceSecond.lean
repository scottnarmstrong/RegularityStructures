/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CompactSpatialSlice
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Identify second spatial slice derivatives with joint coordinate fields. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped ContDiff

 theorem spatial_slice_second_apply {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (t : ℝ) (w v₁ v₂ : Fin 3 → ℝ) :
    fderiv ℝ (fderiv ℝ (fun z : Fin 3 → ℝ => φ (t, z))) w v₁ v₂ =
      fderiv ℝ (fun p : ParabolicSpace => fderiv ℝ φ p (0, v₂)) (t, w) (0, v₁) := by
  let g : (Fin 3 → ℝ) → ℝ := fun z => φ (t, z)
  have hgc := smooth_spatial_slice hφ t
  have hdg : ContDiff ℝ ∞ (fderiv ℝ g) := hgc.fderiv_right (by simp)
  have hc : ContDiff ℝ ∞ (fun p : ParabolicSpace => fderiv ℝ φ p (0, v₂)) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have heval := (ContinuousLinearMap.apply ℝ ℝ v₂).hasFDerivAt.comp w
    (hdg.differentiable (by simp) w).hasFDerivAt
  have hleft := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L v₁) heval.fderiv
  have heq : (fun z => fderiv ℝ g z v₂) =
      (fun z : Fin 3 → ℝ => fderiv ℝ φ (t, z) (0, v₂)) := by
    funext z
    rw [spatial_slice_fderiv (hφ.differentiable (by simp))]
    rfl
  have hright := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L v₁)
    (((hc.differentiable (by simp) (t, w)).hasFDerivAt.comp w
      ((hasFDerivAt_const t w).prodMk (hasFDerivAt_id w))).fderiv)
  change fderiv ℝ (fun z => fderiv ℝ g z v₂) w v₁ =
    fderiv ℝ (fderiv ℝ g) w v₁ v₂ at hleft
  rw [heq] at hleft
  exact hleft.symm.trans hright

end GlobalPhi43.Local
