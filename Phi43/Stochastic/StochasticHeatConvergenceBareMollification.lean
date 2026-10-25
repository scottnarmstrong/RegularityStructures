/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceBareL2
public import Phi43.Stochastic.StochasticHeatConvergenceKernelL2
public import Phi43.Stochastic.StochasticHeatConvergenceMoments

/-!
# Spatial heat regularisation commutes with mollification

The heat-averaged mollified kernel is the space-time convolution of the bare spatially
smoothed kernel with the periodised mollifier. The Fubini integrability is proved from the
boundedness of the mollifier and the unit mass of the massive kernel.
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

theorem integrable_heatKernel_massive_periodise_product
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) (z w : SpaceTime) :
    Integrable (fun q : Torus3 × SpaceTime =>
      heatKernel s q.1 *
        (massiveHeatKernel (((z.1, z.2 - q.1) - w) - q.2) * periodise ρ ε q.2))
      ((volume : Measure Torus3).prod (volume : Measure SpaceTime)) := by
  obtain ⟨B, hB⟩ := bounded_periodise ρ hρ hε
  let D : ℝ := max B 0
  have hPD : ∀ v : SpaceTime, |periodise ρ ε v| ≤ D :=
    fun v => (hB v).trans (le_max_left _ _)
  let F : Torus3 × SpaceTime → ℝ := fun q =>
    heatKernel s q.1 *
      (massiveHeatKernel (((z.1, z.2 - q.1) - w) - q.2) * periodise ρ ε q.2)
  have harg : Measurable (fun q : Torus3 × SpaceTime =>
      ((z.1, z.2 - q.1) - w) - q.2) := by fun_prop
  have hFm : Measurable F :=
    ((measurable_heatKernel_fixed s).comp measurable_fst).mul
      ((measurable_massiveHeatKernel.comp harg).mul
        ((measurable_periodise ρ hρ).comp measurable_snd))
  have hGint (y : Torus3) : Integrable
      (fun v : SpaceTime => massiveHeatKernel (((z.1, z.2 - y) - w) - v)) :=
    integrable_comp_sub_left_spaceTime integrable_massiveHeatKernel _
  have hslice (y : Torus3) : Integrable (fun v : SpaceTime => F (y, v)) := by
    exact ((hGint y).mul_bdd (measurable_periodise ρ hρ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by
        simpa only [Real.norm_eq_abs] using hPD v)).const_mul (heatKernel s y)
  apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hslice, ?_⟩
  have hmajor (y : Torus3) : Integrable (fun v : SpaceTime =>
      heatKernel s y * (massiveHeatKernel (((z.1, z.2 - y) - w) - v) * D)) :=
    ((hGint y).mul_const D).const_mul _
  have hnorm (y : Torus3) : ∫ v : SpaceTime, ‖F (y, v)‖ ≤ heatKernel s y * D := by
    calc
      _ ≤ ∫ v : SpaceTime,
          heatKernel s y * (massiveHeatKernel (((z.1, z.2 - y) - w) - v) * D) := by
        apply integral_mono_ae (hslice y).norm (hmajor y)
        filter_upwards [] with v
        dsimp [F]
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hs y),
          abs_mul, abs_of_nonneg (massiveHeatKernel_nonneg _)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hPD v) (massiveHeatKernel_nonneg _))
            (heatKernel_nonneg hs y)
      _ = heatKernel s y * D := by
        rw [integral_const_mul, integral_mul_const,
          integral_comp_sub_left_spaceTime massiveHeatKernel, integral_massiveHeatKernel,
          one_mul]
  apply ((integrable_heatKernel_fixed hs).mul_const D).mono'
    hFm.aestronglyMeasurable.norm.integral_prod_right'
  filter_upwards [] with y
  rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
  exact hnorm y

theorem stochasticHeatKernel_eq_bare_convolution
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) (z w : SpaceTime) :
    stochasticHeatKernel ρ ε s z w =
      ∫ v : SpaceTime, bareHeatRegularisedKernel s (z - w - v) * periodise ρ ε v := by
  have hprod := integrable_heatKernel_massive_periodise_product ρ hρ hε hs z w
  calc
    _ = ∫ y : Torus3, ∫ v : SpaceTime,
        heatKernel s y *
          (massiveHeatKernel (((z.1, z.2 - y) - w) - v) * periodise ρ ε v) := by
      unfold stochasticHeatKernel mollifiedKernel
      apply integral_congr_ae
      filter_upwards [] with y
      rw [integral_const_mul]
    _ = ∫ v : SpaceTime, ∫ y : Torus3,
        heatKernel s y *
          (massiveHeatKernel (((z.1, z.2 - y) - w) - v) * periodise ρ ε v) :=
      integral_integral_swap hprod
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [bareHeatRegularisedKernel_eq_spatial_integral hs]
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with y
      have harg : ((z.1, z.2 - y) - w) - v =
          ((z - w - v).1, (z - w - v).2 - y) := by
        ext <;> simp
        abel
      rw [harg]
      ring

end RegularityStructures.Phi43

end
