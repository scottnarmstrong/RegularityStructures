/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.MW20.KernelPastSupport
public import GlobalPhi43.MW20.KernelSpatialEven
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Moment cancellation and local integrability for the constructed MW20
kernel measure. No auxiliary probability measure is postulated. -/
public noncomputable section

namespace GlobalPhi43.Local

open MeasureTheory RegularityStructures MW20

/-- A field need only be continuous on the actual compact testing support. -/
theorem integrable_infiniteKernelMeasure_of_continuousOn (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (g : ParabolicSpace → ℝ)
    (hg : ContinuousOn g (tsupport (infiniteKernel Φ hΦ T hT))) :
    Integrable g (infiniteKernelMeasure Φ hΦ T hT) := by
  let K := infiniteKernel Φ hΦ T hT
  have hK : Continuous K := K.continuous
  have hc : HasCompactSupport K := infiniteKernel_hasCompactSupport Φ hΦ hT hT₁
  have hint : Integrable (fun z => K z * g z) (volume : Measure ParabolicSpace) := by
    have hi := ((hK.continuousOn).mul hg).integrableOn_compact (μ := (volume : Measure ParabolicSpace)) hc
    apply hi.integrable_of_forall_notMem_eq_zero
    intro z hz
    have he : K z = 0 := by
      by_contra hn
      exact hz (subset_tsupport K hn)
    simp [he]
  unfold infiniteKernelMeasure
  apply (integrable_withDensity_iff_integrable_smul'
    (ENNReal.measurable_ofReal.comp hK.measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).2
  have hn (z : ParabolicSpace) : 0 ≤ K z := infiniteKernel_nonneg Φ hΦ hT hT₁ z
  simpa only [Function.comp_apply, ENNReal.toReal_ofReal (hn _), smul_eq_mul] using hint

/-- Every spatial coordinate is integrable for the actual infinite measure. -/
theorem infiniteKernelMeasure_coordinate_integrable (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (i : Fin 3) :
    Integrable (fun z : ParabolicSpace => z.2 i) (infiniteKernelMeasure Φ hΦ T hT) :=
  integrable_infiniteKernelMeasure_of_continuousOn Φ hΦ hT hT₁ _ (by fun_prop)

/-- Spatial evenness cancels each first moment exactly. -/
theorem integral_coordinate_infiniteKernelMeasure_eq_zero (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (i : Fin 3) :
    ∫ z : ParabolicSpace, z.2 i ∂infiniteKernelMeasure Φ hΦ T hT = 0 := by
  rw [integral_infiniteKernelMeasure Φ hΦ hT hT₁]
  have hi := integral_spatialReflect (fun z => infiniteKernel Φ hΦ T hT z * z.2 i)
  have he (z : ParabolicSpace) : infiniteKernel Φ hΦ T hT (parabolicDilate (-1) z) *
      (parabolicDilate (-1) z).2 i = -(infiniteKernel Φ hΦ T hT z * z.2 i) := by
    rw [infiniteKernel_spatialReflect Φ hΦ hT hT₁]
    simp [parabolicDilate]
  simp_rw [he, integral_neg] at hi
  linarith

end GlobalPhi43.Local
