/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.HeatOpBridge
public import RegularityStructures.PDE.Duhamel
public import RegularityStructures.Analysis.Heat.Kernel
public import RegularityStructures.Abstract.FixedPointTimeSlab
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The `ℝ⁴` heat potential of a spatially periodic function is the torus Duhamel integral

For a continuous path `h : ℝ → C(T³)` and a function `G` on
`ℝ × ℝ³` with `G(r, y) = h_r(y mod ℤ³)` for `0 < r ≤ T`,
`∫_{ℝ⁴} H((t, x) - z) 𝟙_{(0,T]×ℝ³}(z) G(z) dz = ∫₀ᵗ P_{t-r} h_r (x) dr = duhamel h t (x)`
for `0 < t ≤ T`, where `H = heatKernelR4` (`heatPotential_eq_duhamel`).
-/

public section

open MeasureTheory Set Filter RegularityStructures.PDE

namespace RegularityStructures.Phi43

/-- The inner (spatial) integral: `∫ γ_τ(x - y) g(y mod ℤ³) dy = (P_τ g)(x)`. -/
theorem integral_gaussKernel_sub_torus {τ : ℝ} (hτ : 0 < τ) (g : C(Torus3, ℝ)) (x : Fin 3 → ℝ) :
    ∫ y, gaussKernel τ (x - y) * g (torusProj y) = heatOp τ g (torusProj x) := by
  rw [heatOp_eq_heatSemigroup hτ, heatSemigroup]
  rw [← integral_sub_left_eq_self (fun y => gaussKernel τ y * g (torusProj x - torusProj y))
    (volume : Measure (Fin 3 → ℝ)) x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [torusProj_sub, sub_sub_cancel]


/-- The integrand of the heat potential, as an explicit function. -/
private noncomputable def potIntegrand (h : ℝ → C(Torus3, ℝ)) (t : ℝ) (x : Fin 3 → ℝ)
    (z : ParabolicSpace) : ℝ :=
  if z.1 ∈ Ioo 0 t then gaussKernel (t - z.1) (x - z.2) * h z.1 (torusProj z.2) else 0

private theorem measurable_potIntegrand {h : ℝ → C(Torus3, ℝ)} (hh : Continuous h) (t : ℝ)
    (x : Fin 3 → ℝ) : Measurable (potIntegrand h t x) := by
  unfold potIntegrand
  refine Measurable.ite (measurableSet_Ioo.preimage measurable_fst) ?_ measurable_const
  refine Measurable.mul ?_ ?_
  · unfold gaussKernel sqNorm3
    fun_prop
  · exact (continuous_eval.comp ((hh.comp continuous_fst).prodMk
      (continuous_torusProj.comp continuous_snd))).measurable

private theorem potIntegrand_eq (h : ℝ → C(Torus3, ℝ)) {T t : ℝ} (htT : t ≤ T)
    (G : ParabolicSpace → ℝ) (hG : ∀ r ∈ Ioc 0 T, ∀ y, G (r, y) = h r (torusProj y))
    (x : Fin 3 → ℝ) (z : ParabolicSpace) :
    heatKernelR4 (((t, x) : ParabolicSpace) - z) * (timeSlab T).indicator G z =
      potIntegrand h t x z := by
  unfold potIntegrand
  by_cases hz : z.1 ∈ Ioo 0 t
  · simp only [hz, ↓reduceIte]
    have hzs : z ∈ timeSlab T := ⟨hz.1, hz.2.le.trans htT⟩
    rw [indicator_of_mem hzs, heatKernelR4_of_pos (by simp [hz.2]), hG z.1 ⟨hz.1, hz.2.le.trans htT⟩]
    rfl
  · simp only [hz, ↓reduceIte]
    by_cases h0 : 0 < z.1
    · have : t ≤ z.1 := by
        by_contra hlt
        exact hz ⟨h0, not_le.1 hlt⟩
      rw [heatKernelR4_of_nonpos (by simp [this]), zero_mul]
    · have hzs : z ∉ timeSlab T := fun hh => h0 hh.1
      rw [indicator_of_notMem hzs, mul_zero]

theorem heatPotential_eq_duhamel (h : ℝ → C(Torus3, ℝ)) (hh : Continuous h) {T t : ℝ}
    (ht0 : 0 < t) (htT : t ≤ T) (G : ParabolicSpace → ℝ)
    (hG : ∀ r ∈ Ioc 0 T, ∀ y, G (r, y) = h r (torusProj y)) (x : Fin 3 → ℝ) :
    ∫ z : ParabolicSpace, heatKernelR4 (((t, x) : ParabolicSpace) - z) *
        (timeSlab T).indicator G z = duhamel h t (torusProj x) := by
  simp_rw [potIntegrand_eq h htT G hG x]
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hh.continuousOn
  have hM0 : 0 ≤ M := by
    have := hM 0 ⟨le_rfl, ht0.le.trans htT⟩
    exact (norm_nonneg _).trans this
  have hmeas := measurable_potIntegrand hh t x
  -- the dominating function
  set B : ParabolicSpace → ℝ := fun z =>
    if z.1 ∈ Ioo 0 t then M * gaussKernel (t - z.1) (x - z.2) else 0 with hB
  have hBint : Integrable B (volume : Measure ParabolicSpace) := by
    rw [Measure.volume_eq_prod]
    have hBm : Measurable B := by
      refine Measurable.ite (measurableSet_Ioo.preimage measurable_fst) ?_ measurable_const
      refine Measurable.const_mul ?_ _
      unfold gaussKernel sqNorm3
      fun_prop
    rw [integrable_prod_iff hBm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun r => ?_, ?_⟩
    · by_cases hr : r ∈ Ioo 0 t
      · simp only [hB, hr, ↓reduceIte]
        exact ((integrable_gaussKernel (sub_pos.2 hr.2)).comp_sub_left x).const_mul M
      · simp only [hB, hr, ↓reduceIte]
        exact integrable_zero _ _ _
    · have : (fun r : ℝ => ∫ y : Fin 3 → ℝ, ‖B (r, y)‖) = (Ioo 0 t).indicator (fun _ => M) := by
        funext r
        by_cases hr : r ∈ Ioo 0 t
        · simp only [hB, hr, ↓reduceIte, indicator_of_mem hr]
          have hτ := sub_pos.2 hr.2
          have : ∀ y : Fin 3 → ℝ, ‖M * gaussKernel (t - r) (x - y)‖ = M * gaussKernel (t - r) (x - y) :=
            fun y => by
              rw [Real.norm_of_nonneg (mul_nonneg hM0 (gaussKernel_nonneg hτ _))]
          simp_rw [this]
          rw [integral_const_mul, integral_sub_left_eq_self (fun y => gaussKernel (t - r) y)
            (volume : Measure (Fin 3 → ℝ)) x, integral_gaussKernel hτ, mul_one]
        · simp only [hB, hr, ↓reduceIte, indicator_of_notMem hr, norm_zero, integral_zero]
      rw [this]
      exact (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp) (by simp))
  have hFint : Integrable (potIntegrand h t x) (volume : Measure ParabolicSpace) := by
    refine hBint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    unfold potIntegrand
    by_cases hz : z.1 ∈ Ioo 0 t
    · simp only [hB, hz, ↓reduceIte]
      have hτ := sub_pos.2 hz.2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussKernel_nonneg hτ _), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (gaussKernel_nonneg hτ _)
      exact ((h z.1).norm_coe_le_norm _).trans (hM z.1 ⟨hz.1.le, hz.2.le.trans htT⟩)
    · simp only [hB, hz, ↓reduceIte, norm_zero]
      exact le_rfl
  rw [Measure.volume_eq_prod] at hFint ⊢
  rw [integral_prod _ hFint]
  have hinner : ∀ r : ℝ, ∫ y : Fin 3 → ℝ, potIntegrand h t x (r, y) =
      (Ioo 0 t).indicator (fun r => heatOp (t - r) (h r) (torusProj x)) r := by
    intro r
    by_cases hr : r ∈ Ioo 0 t
    · rw [indicator_of_mem hr]
      simp only [potIntegrand, hr, ↓reduceIte]
      exact integral_gaussKernel_sub_torus (sub_pos.2 hr.2) (h r) x
    · rw [indicator_of_notMem hr]
      simp only [potIntegrand, hr, ↓reduceIte, integral_zero]
  simp_rw [hinner]
  rw [duhamel_apply hh, intervalIntegral.integral_of_le ht0.le, integral_indicator measurableSet_Ioo,
    integral_Ioc_eq_integral_Ioo]

end RegularityStructures.Phi43

end
