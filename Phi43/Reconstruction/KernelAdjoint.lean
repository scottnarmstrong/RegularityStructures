/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.RemainderIBP
public import Phi43.Structure.CanonicalKernelHairer
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The adjoint equation for the singular kernel `K = K_N`

`integral_hairerKernel_lstar`: for a smooth space-periodic `ψ` vanishing for `|t| > b`,
`∫ K(w) (L^*ψ)(w) dw = ψ(0) - ∫ Q(w) ψ(w) dw`, `Q = (∂_t - Δ) R`, i.e. `(∂_t - Δ) K = δ - Q`
in the sense of distributions tested against periodic functions.  It follows from `K = G - R`,
`∫ G L^*ψ = ψ(0)` (`fundamentalSolution_periodic`) and `∫ R L^*ψ = ∫ Q ψ`
(`integral_annRemainder_lstar`).
-/

public section

open Set MeasureTheory Filter RegularityStructures.Inhomogeneity RegularityStructures.Potential
open scoped ContDiff

namespace RegularityStructures.Phi43

/-- The heat kernel times a bounded function supported in `|t| ≤ b` is integrable. -/
theorem integrable_heatKernel_mul {φ : ParabolicSpace → ℝ} (hφ : Continuous φ) {b M : ℝ}
    (hφb : ∀ w, |φ w| ≤ M) (hφs : ∀ w : ParabolicSpace, b < |w.1| → φ w = 0) :
    Integrable (fun w => heatKernelR4 w * φ w) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hφb 0)
  have hm : Measurable fun w : ParabolicSpace => heatKernelR4 w * φ w :=
    measurable_heatKernelR4.mul hφ.measurable
  rw [Measure.volume_eq_prod]
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun r => ?_, ?_⟩
  · by_cases hr : 0 < r
    · have h1 : Integrable (fun y : Fin 3 → ℝ => gaussKernel r y) := integrable_gaussKernel hr
      refine (h1.mul_const M).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
      · exact (measurable_heatKernelR4.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.mul
          (hφ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, heatKernelR4_of_pos (by simpa using hr)]
        change |gaussKernel r y| * |φ (r, y)| ≤ _
        rw [abs_of_nonneg (gaussKernel_nonneg hr _)]
        exact mul_le_mul_of_nonneg_left (hφb _) (gaussKernel_nonneg hr _)
    · have : (fun y : Fin 3 → ℝ => heatKernelR4 (r, y) * φ (r, y)) = fun _ => 0 := by
        funext y; rw [heatKernelR4_of_nonpos (by simpa using hr), zero_mul]
      rw [this]; exact integrable_zero _ _ _
  · have hb : ∀ r : ℝ, ∫ y : Fin 3 → ℝ, ‖heatKernelR4 (r, y) * φ (r, y)‖ ≤
        (Ioc 0 b).indicator (fun _ => M) r := by
      intro r
      by_cases hr : r ∈ Ioc 0 b
      · rw [indicator_of_mem hr]
        have hr0 := hr.1
        calc ∫ y : Fin 3 → ℝ, ‖heatKernelR4 (r, y) * φ (r, y)‖ ≤ ∫ y : Fin 3 → ℝ, gaussKernel r y * M := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
                ((integrable_gaussKernel hr0).mul_const M) (Filter.Eventually.of_forall fun y => ?_)
              show ‖heatKernelR4 (r, y) * φ (r, y)‖ ≤ gaussKernel r y * M
              rw [Real.norm_eq_abs, abs_mul, heatKernelR4_of_pos (by simpa using hr0)]
              change |gaussKernel r y| * |φ (r, y)| ≤ _
              rw [abs_of_nonneg (gaussKernel_nonneg hr0 _)]
              exact mul_le_mul_of_nonneg_left (hφb _) (gaussKernel_nonneg hr0 _)
          _ = M := by rw [integral_mul_const, integral_gaussKernel hr0, one_mul]
      · rw [indicator_of_notMem hr]
        by_cases h0 : 0 < r
        · have hbr : b < |r| := by
            rw [abs_of_pos h0]; exact not_le.1 fun h => hr ⟨h0, h⟩
          have : (fun y : Fin 3 → ℝ => ‖heatKernelR4 (r, y) * φ (r, y)‖) = fun _ => 0 := by
            funext y; rw [hφs (r, y) hbr]; simp
          rw [this]; simp
        · have : (fun y : Fin 3 → ℝ => ‖heatKernelR4 (r, y) * φ (r, y)‖) = fun _ => 0 := by
            funext y; rw [heatKernelR4_of_nonpos (by simpa using h0)]; simp
          rw [this]; simp
    refine Integrable.mono' (g := (Ioc 0 b).indicator fun _ => M)
      ((integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp) enorm_ne_top)) ?_
      (Filter.Eventually.of_forall fun r => ?_)
    · exact (hm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      exact hb r

theorem lstar_eq_zero_of_support {ψ : ParabolicSpace → ℝ} {b : ℝ}
    (hs : ∀ w : ParabolicSpace, b < |w.1| → ψ w = 0) :
    ∀ w : ParabolicSpace, b < |w.1| → lstar ψ w = 0 := by
  intro w hw
  unfold lstar
  rw [ddv_eq_zero_of_support hs 0 w hw]
  simp only [neg_zero, zero_sub, neg_eq_zero]
  exact Finset.sum_eq_zero fun j _ =>
    ddv_eq_zero_of_support (ddv_eq_zero_of_support hs j.succ) j.succ w hw

/-- **`(∂_t - Δ) K = δ - Q`** against periodic test functions. -/
theorem integral_hairerKernel_lstar (N : ℕ) {ψ : ParabolicSpace → ℝ} (hψ : PerSmooth ψ) {b : ℝ}
    (hb : 0 ≤ b) (hs : ∀ w : ParabolicSpace, b < |w.1| → ψ w = 0) :
    ∫ w, hairerKernel N w * lstar ψ w = ψ 0 - ∫ w, potQ N w * ψ w := by
  have hL := perSmooth_lstar hψ
  have hLs := lstar_eq_zero_of_support hs
  obtain ⟨M, -, hM⟩ := exists_bound_of_support hL hLs
  have hG := integrable_heatKernel_mul hL.smooth.continuous hM hLs
  have hR : Integrable (fun w => annRemainderC N w * lstar ψ w) := by
    have := integrable_ddA_mul N [] hL hLs
    simpa [ddA] using this
  have e : (fun w => hairerKernel N w * lstar ψ w) =ᵐ[volume]
      fun w => heatKernelR4 w * lstar ψ w - annRemainderC N w * lstar ψ w := by
    have hna : NullSingletonClass (volume : Measure ParabolicSpace) := by
      rw [Measure.volume_eq_prod]; infer_instance
    filter_upwards [(Set.countable_singleton (0 : ParabolicSpace)).ae_notMem volume] with w hw
    rw [hairerKernel_eq_heat_sub_remainder (by simpa using hw)]
    ring
  rw [integral_congr_ae e, integral_sub hG hR,
    fundamentalSolution_periodic hψ hb hs, integral_annRemainder_lstar N hψ hs]

end RegularityStructures.Phi43

end
