/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.TranslatedKernelTaylor
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual integrability of compact-kernel values and affine coefficients. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MeasureTheory
open scoped ContDiff

 theorem kernel_weighted_integrable {k : ParabolicSpace → ℝ}
    (hk : ContDiff ℝ ∞ k) (hck : HasCompactSupport k) {μ : Measure ParabolicSpace}
    {g : ParabolicSpace → ℝ} (hg : Integrable g μ) (x : ParabolicSpace) :
    Integrable (fun q => k (x - q) * g q) μ := by
  obtain ⟨B, hB⟩ := hk.continuous.bounded_above_of_compact_support hck
  exact hg.bdd_mul (by fun_prop : Continuous (fun q => k (x - q))).aestronglyMeasurable
    (ae_of_all _ fun q => hB (x - q))

 theorem kernel_gradient_weighted_integrable {k : ParabolicSpace → ℝ}
    (hk : ContDiff ℝ ∞ k) (hck : HasCompactSupport k) {μ : Measure ParabolicSpace}
    {g : ParabolicSpace → ℝ} (hg : Integrable g μ) (x v : ParabolicSpace) :
    Integrable (fun q => fderiv ℝ k (x - q) v * g q) μ := by
  have hdk : ContDiff ℝ ∞ (fderiv ℝ k) := hk.fderiv_right (by simp)
  obtain ⟨B, hB⟩ := hdk.continuous.bounded_above_of_compact_support (hck.fderiv ℝ)
  apply hg.bdd_mul (c := B * ‖v‖) (by fun_prop : Continuous (fun q => fderiv ℝ k (x - q) v)).aestronglyMeasurable
  exact ae_of_all _ fun q => ((fderiv ℝ k (x - q)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hB (x - q)) (norm_nonneg v))

end GlobalPhi43.Local
