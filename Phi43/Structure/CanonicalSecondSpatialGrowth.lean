/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalGlobalDerivativeGrowth
public import Phi43.Structure.CanonicalConvolutionDerivativeGrowth
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Phi43.Structure.CanonicalSmoothCharacters

/-!
# Second spatial envelopes for the smooth canonical lift

The Gamma coefficients of `I(Ψ)Ψ` and its products require one spatial
increment of the spatial gradient of `K * Ψ`.  This module isolates that
ordinary smooth estimate.  It is a source-derived analytic helper, not an
abstract model-bound hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Topology Pointwise

namespace RegularityStructures.Phi43

def phi43SpatialVector (i : Fin 3) : ParabolicSpace := (0, Pi.single i 1)

def phi43SpatialDerivative (f : ParabolicSpace → ℝ) (i : Fin 3) :
    ParabolicSpace → ℝ := fun z => fderiv ℝ f z (phi43SpatialVector i)

open scoped ContDiff in
private theorem spatialDerivative_contDiff {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (phi43SpatialDerivative f i) := by
  unfold phi43SpatialDerivative
  have hc : ContDiff ℝ ∞ (fun z : ParabolicSpace =>
      (z, phi43SpatialVector i)) := contDiff_id.prodMk contDiff_const
  simpa [Function.comp_def] using
    (hf.contDiff_fderiv_apply (m := (⊤ : ℕ∞)) (by simp)).comp hc

open scoped ContDiff in
private theorem integrable_hairerKernel_smul_fderiv_at
    (N : ℕ) {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (z : ParabolicSpace) :
    Integrable (fun w => hairerKernel N w • fderiv ℝ f (z - w)) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hc := canonicalHairerKernel_hasCompactSupport N
  have hi := canonicalHairerKernel_integrable N
  let S : Set ParabolicSpace := ({z} : Set ParabolicSpace) +
    -tsupport (hairerKernel N)
  have hS : IsCompact S := (isCompact_singleton (x := z)).add hc.isCompact.neg
  obtain ⟨D, hD⟩ := hS.exists_bound_of_continuousOn hfd.continuousOn
  have hd (w : ParabolicSpace) (hw : hairerKernel N w ≠ 0) :
      ‖fderiv ℝ f (z - w)‖ ≤ max D 0 := by
    apply (hD (z - w) ?_).trans (le_max_left _ _)
    refine Set.mem_add.2 ⟨z, Set.mem_singleton z, -w, ?_, by abel⟩
    simpa only [Set.mem_neg, neg_neg] using
      (subset_tsupport (hairerKernel N) hw :
        w ∈ tsupport (hairerKernel N))
  have hmeas :
      AEStronglyMeasurable
        (fun w => hairerKernel N w • fderiv ℝ f (z - w)) :=
    hi.aestronglyMeasurable.smul
      ((hfd.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  refine hi.abs.mul_const (max D 0) |>.mono' hmeas ?_
  filter_upwards [] with w
  rw [norm_smul, Real.norm_eq_abs]
  by_cases hw : hairerKernel N w = 0
  · rw [hw]
    simp only [abs_zero, zero_mul]
    exact le_refl 0
  · exact mul_le_mul_of_nonneg_left (hd w hw) (abs_nonneg _)

open scoped ContDiff in
/-- The spatial derivative of the actual convolution is the convolution of
the corresponding directional derivative of its input. -/
theorem hairerSpatialGradient_eq_hairerConvolution_spatialDerivative
    (N : ℕ) {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    hairerSpatialGradient N f i = hairerConvolution N (phi43SpatialDerivative f i) := by
  funext z
  rw [hairerSpatialGradient_eq_fderiv N hf i, fderiv_hairerConvolution N hf]
  rw [ContinuousLinearMap.integral_apply]
  · rw [hairerConvolution_eq_convolution, convolution_def]
    simp only [phi43SpatialDerivative, phi43SpatialVector, smul_apply, smul_eq_mul]
    rfl
  · exact integrable_hairerKernel_smul_fderiv_at N hf z

open scoped ContDiff in
/-- A polynomial envelope for one more spatial derivative of the integrated
convolution, supplied by polynomial envelopes for the input directional
derivative and its derivative. -/
theorem canonicalPolyBounded_fderiv_hairerSpatialGradient
    (N : ℕ) {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (i : Fin 3)
    (hdf : PolyBounded (fun z => ‖fderiv ℝ (phi43SpatialDerivative f i) z‖)) :
    PolyBounded (fun z => ‖fderiv ℝ (hairerSpatialGradient N f i) z‖) := by
  rw [hairerSpatialGradient_eq_hairerConvolution_spatialDerivative N hf i]
  exact canonicalPolyBounded_norm_fderiv_convolution N
    (spatialDerivative_contDiff hf i) hdf

end RegularityStructures.Phi43

end
