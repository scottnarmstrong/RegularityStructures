/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatOperatorRegularity
public import GlobalPhi43.Local.PastAffineShift

/-! A spatial affine comparison is smooth and does not alter sourceHeat. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20
open scoped ContDiff

 def spatialAffineDifferential (ν : Fin 3 → ℝ) : ParabolicSpace →L[ℝ] ℝ :=
  ∑ i : Fin 3, ν i • ((ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)))

 theorem spatialAffineDifferential_apply (ν : Fin 3 → ℝ) (p : ParabolicSpace) :
    spatialAffineDifferential ν p = spatialLinear ν p := by
  simp [spatialAffineDifferential, spatialLinear]

 theorem spatialAffineDifferential_time (ν : Fin 3 → ℝ) : spatialAffineDifferential ν (1, 0) = 0 := by
  simp [spatialAffineDifferential]

 theorem spatialAffine_contDiff (x : ParabolicSpace) (c : ℝ) (ν : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (spatialAffine x c ν) := by
  have hh : ContDiff ℝ ∞ (fun p : ParabolicSpace => c + spatialAffineDifferential ν (p - x)) :=
    contDiff_const.add ((spatialAffineDifferential ν).contDiff.comp (contDiff_id.sub contDiff_const))
  simpa only [spatialAffineDifferential_apply, spatialAffine] using! hh

 theorem spatialAffine_hasFDerivAt (x : ParabolicSpace) (c : ℝ) (ν : Fin 3 → ℝ) (q : ParabolicSpace) :
    HasFDerivAt (spatialAffine x c ν) (spatialAffineDifferential ν) q := by
  have hh := (hasFDerivAt_const c q).add
    ((spatialAffineDifferential ν).hasFDerivAt.comp q ((hasFDerivAt_id q).sub_const x))
  simpa only [spatialAffineDifferential_apply, spatialAffine, ContinuousLinearMap.comp_id, zero_add] using! hh

 theorem sourceHeat_sub_spatialAffine {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : ParabolicSpace) (c : ℝ) (ν : Fin 3 → ℝ) (q : ParabolicSpace) :
    sourceHeat (fun p => f p - spatialAffine x c ν p) q = sourceHeat f q := by
  have hlin := spatialAffine_contDiff x c ν
  have hdf : fderiv ℝ (fun p => f p - spatialAffine x c ν p) =
      fun p => fderiv ℝ f p - spatialAffineDifferential ν := by
    funext p
    exact ((hf.differentiable (by simp) p).hasFDerivAt.sub (spatialAffine_hasFDerivAt x c ν p)).fderiv
  have hfderiv : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdd : fderiv ℝ (fderiv ℝ (fun p => f p - spatialAffine x c ν p)) q =
      fderiv ℝ (fderiv ℝ f) q := by
    rw [hdf]
    exact ((hfderiv.differentiable (by simp) q).hasFDerivAt.sub_const (spatialAffineDifferential ν)).fderiv
  rw [sourceHeat_eq_fderiv_of_contDiffAt _ q ((hf.sub hlin).contDiffAt.of_le (by norm_num)),
    sourceHeat_eq_fderiv_of_contDiffAt f q (hf.contDiffAt.of_le (by norm_num)), hdd, hdf]
  simp only [sub_apply, spatialAffineDifferential_time, sub_zero]

end GlobalPhi43.Local
