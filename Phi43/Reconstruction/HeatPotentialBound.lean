/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Kernel
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.PDE.HeatOp
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A bound for the `ℝ⁴` heat potential of a function with a time-singular bound

For `G` with `|G(r, y)| ≤ g(r)` on the slab `0 < r ≤ T` and `0 < t ≤ T`,
`|∫ H((t, x) - z) 𝟙_{slab}(z) G(z) dz| ≤ ∫₀ᵗ g(r) dr` (`abs_heatPotential_le`): the spatial
integral of the heat kernel is `1` on each time slice.  Used for the behaviour at `t → 0`
of the reconstruction (`g(r) = C r^{3η/2}`, `3η/2 > -1`).
-/

public section

open MeasureTheory Set Filter

namespace RegularityStructures.Phi43

private noncomputable def potBound (g : ℝ → ℝ) (t : ℝ) (x : Fin 3 → ℝ) (z : ParabolicSpace) : ℝ :=
  if z.1 ∈ Ioo 0 t then g z.1 * gaussKernel (t - z.1) (x - z.2) else 0

private theorem integrable_potBound {g : ℝ → ℝ} (hg0 : ∀ r, 0 ≤ g r) (hgm : Measurable g)
    {t : ℝ} (hgi : IntervalIntegrable g volume 0 t) (x : Fin 3 → ℝ) :
    Integrable (potBound g t x) (volume : Measure ParabolicSpace) := by
  rw [Measure.volume_eq_prod]
  have hBm : Measurable (potBound g t x) := by
    unfold potBound
    refine Measurable.ite (measurableSet_Ioo.preimage measurable_fst) ?_ measurable_const
    refine Measurable.mul (hgm.comp measurable_fst) ?_
    unfold gaussKernel sqNorm3
    fun_prop
  rw [integrable_prod_iff hBm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun r => ?_, ?_⟩
  · by_cases hr : r ∈ Ioo 0 t
    · simp only [potBound, hr, ↓reduceIte]
      exact ((integrable_gaussKernel (sub_pos.2 hr.2)).comp_sub_left x).const_mul (g r)
    · simp only [potBound, hr, ↓reduceIte]
      exact integrable_zero _ _ _
  · have : (fun r : ℝ => ∫ y : Fin 3 → ℝ, ‖potBound g t x (r, y)‖) =
        (Ioo 0 t).indicator g := by
      funext r
      by_cases hr : r ∈ Ioo 0 t
      · simp only [potBound, hr, ↓reduceIte, indicator_of_mem hr]
        have hτ := sub_pos.2 hr.2
        have : ∀ y : Fin 3 → ℝ, ‖g r * gaussKernel (t - r) (x - y)‖ =
            g r * gaussKernel (t - r) (x - y) := fun y => by
          rw [Real.norm_of_nonneg (mul_nonneg (hg0 r) (gaussKernel_nonneg hτ _))]
        simp_rw [this]
        rw [integral_const_mul, integral_sub_left_eq_self (fun y => gaussKernel (t - r) y)
          (volume : Measure (Fin 3 → ℝ)) x, integral_gaussKernel hτ, mul_one]
      · simp only [potBound, hr, ↓reduceIte, indicator_of_notMem hr, norm_zero, integral_zero]
    rw [this]
    exact (integrable_indicator_iff measurableSet_Ioo).2
      (by simpa [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Ioc] using
        hgi.1)

private theorem integral_potBound_slice {g : ℝ → ℝ} (r : ℝ) (t : ℝ) (x : Fin 3 → ℝ) :
    ∫ y : Fin 3 → ℝ, potBound g t x (r, y) = (Ioo 0 t).indicator g r := by
  by_cases hr : r ∈ Ioo 0 t
  · simp only [potBound, hr, ↓reduceIte, indicator_of_mem hr]
    have hτ := sub_pos.2 hr.2
    rw [integral_const_mul, integral_sub_left_eq_self (fun y => gaussKernel (t - r) y)
      (volume : Measure (Fin 3 → ℝ)) x, integral_gaussKernel hτ, mul_one]
  · simp only [potBound, hr, ↓reduceIte, indicator_of_notMem hr, integral_zero]

theorem abs_heatPotential_le {g : ℝ → ℝ} (hg0 : ∀ r, 0 ≤ g r) (hgm : Measurable g) {t T : ℝ}
    (ht0 : 0 < t) (htT : t ≤ T) (hgi : IntervalIntegrable g volume 0 t)
    (G : ParabolicSpace → ℝ) (hG : ∀ r ∈ Ioc 0 t, ∀ y, |G (r, y)| ≤ g r) (x : Fin 3 → ℝ) :
    |∫ z : ParabolicSpace, heatKernelR4 (((t, x) : ParabolicSpace) - z) *
        (timeSlab T).indicator G z| ≤ ∫ r in (0 : ℝ)..t, g r := by
  have hB := integrable_potBound hg0 hgm hgi x
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hB (Filter.Eventually.of_forall fun z => ?_)).trans ?_
  · unfold potBound
    by_cases hz : z.1 ∈ Ioo 0 t
    · simp only [hz, ↓reduceIte]
      have hτ := sub_pos.2 hz.2
      have hzs : z ∈ timeSlab T := ⟨hz.1, hz.2.le.trans htT⟩
      rw [indicator_of_mem hzs, heatKernelR4_of_pos (by simp [hz.2]), Real.norm_eq_abs, abs_mul]
      change |gaussKernel (t - z.1) (x - z.2)| * |G z| ≤ _
      rw [abs_of_nonneg (gaussKernel_nonneg hτ _), mul_comm]
      exact mul_le_mul_of_nonneg_right ((hG z.1 ⟨hz.1, hz.2.le⟩ z.2))
        (gaussKernel_nonneg hτ _)
    · simp only [hz, ↓reduceIte]
      by_cases h0 : 0 < z.1
      · have : t ≤ z.1 := by
          by_contra hlt
          exact hz ⟨h0, not_le.1 hlt⟩
        rw [heatKernelR4_of_nonpos (by simp [this]), zero_mul, norm_zero]
      · have hzs : z ∉ timeSlab T := fun hh => h0 hh.1
        rw [indicator_of_notMem hzs, mul_zero, norm_zero]
  · rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hB)]
    simp_rw [integral_potBound_slice]
    rw [integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le ht0.le,
      integral_Ioc_eq_integral_Ioo]

private theorem norm_integrand_le_potBound {g : ℝ → ℝ} {t T : ℝ} (htT : t ≤ T)
    (G : ParabolicSpace → ℝ) (hG : ∀ r ∈ Ioc 0 t, ∀ y, |G (r, y)| ≤ g r) (x : Fin 3 → ℝ)
    (z : ParabolicSpace) :
    ‖heatKernelR4 (((t, x) : ParabolicSpace) - z) * (timeSlab T).indicator G z‖ ≤
      potBound g t x z := by
  unfold potBound
  by_cases hz : z.1 ∈ Ioo 0 t
  · simp only [hz, ↓reduceIte]
    have hτ := sub_pos.2 hz.2
    have hzs : z ∈ timeSlab T := ⟨hz.1, hz.2.le.trans htT⟩
    rw [indicator_of_mem hzs, heatKernelR4_of_pos (by simp [hz.2]), Real.norm_eq_abs, abs_mul]
    change |gaussKernel (t - z.1) (x - z.2)| * |G z| ≤ _
    rw [abs_of_nonneg (gaussKernel_nonneg hτ _), mul_comm]
    exact mul_le_mul_of_nonneg_right ((hG z.1 ⟨hz.1, hz.2.le⟩ z.2)) (gaussKernel_nonneg hτ _)
  · simp only [hz, ↓reduceIte]
    by_cases h0 : 0 < z.1
    · have : t ≤ z.1 := by
        by_contra hlt
        exact hz ⟨h0, not_le.1 hlt⟩
      rw [heatKernelR4_of_nonpos (by simp [this]), zero_mul, norm_zero]
    · have hzs : z ∉ timeSlab T := fun hh => h0 hh.1
      rw [indicator_of_notMem hzs, mul_zero, norm_zero]

/-- The heat potential integrand is integrable. -/
theorem integrable_heatPotential {g : ℝ → ℝ} (hg0 : ∀ r, 0 ≤ g r) (hgm : Measurable g) {t T : ℝ}
    (htT : t ≤ T) (hgi : IntervalIntegrable g volume 0 t) (G : ParabolicSpace → ℝ)
    (hGm : Measurable G) (hG : ∀ r ∈ Ioc 0 t, ∀ y, |G (r, y)| ≤ g r) (x : Fin 3 → ℝ) :
    Integrable (fun z : ParabolicSpace => heatKernelR4 (((t, x) : ParabolicSpace) - z) *
      (timeSlab T).indicator G z) := by
  refine (integrable_potBound hg0 hgm hgi x).mono' ?_
    (Filter.Eventually.of_forall (norm_integrand_le_potBound htT G hG x))
  refine Measurable.aestronglyMeasurable (Measurable.mul ?_ (hGm.indicator ?_))
  · exact measurable_heatKernelR4.comp (measurable_const.sub measurable_id)
  · exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)

end RegularityStructures.Phi43

end
