/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RegularityStructures.PDE.HeatTime
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Normed.Group.Bounded
public import RegularityStructures.Analysis.Parabolic.Basic

/-! Compact smooth space-time tests have compact smooth spatial slices. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped ContDiff

def heatSpatialInsert : (Fin 3 → ℝ) →L[ℝ] ParabolicSpace :=
  (0 : (Fin 3 → ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Fin 3 → ℝ))

theorem compact_spatial_slice {φ : ParabolicSpace → ℝ} (hφ : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (fun w : Fin 3 → ℝ => φ (t, w)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hφ.isCompact.image continuous_snd)
  intro w hw
  exact ⟨(t, w), subset_tsupport φ hw, rfl⟩

theorem smooth_spatial_slice {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (t : ℝ) :
    ContDiff ℝ ∞ (fun w : Fin 3 → ℝ => φ (t, w)) :=
  hφ.comp (contDiff_const.prodMk contDiff_id)

theorem spatial_slice_fderiv {φ : ParabolicSpace → ℝ} (hφ : Differentiable ℝ φ)
    (t : ℝ) (w : Fin 3 → ℝ) :
    fderiv ℝ (fun z : Fin 3 → ℝ => φ (t, z)) w =
      (fderiv ℝ φ (t, w)).comp heatSpatialInsert := by
  exact ((hφ (t, w)).hasFDerivAt.comp w
    ((hasFDerivAt_const t w).prodMk (hasFDerivAt_id w))).fderiv

end GlobalPhi43.Local
