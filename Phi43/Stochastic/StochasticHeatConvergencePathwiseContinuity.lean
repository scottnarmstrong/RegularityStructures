/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergencePastContinuity
import Mathlib.Analysis.Convolution
import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous pathwise massive heat convolutions

A continuous forcing with an exponentially integrable past defines a continuous massive heat
convolution. Locally, clamp the forcing to a compact time interval. Its convolution is continuous
by the integrable-kernel theorem; the remaining remote-past term is continuous by domination.
The massive kernel is that of equation (2.2) of the statement.
-/

public noncomputable section

open MeasureTheory Real Set
open scoped Topology Convolution

namespace RegularityStructures.Phi43

private theorem exp_past_integrable (a : ℝ) :
    IntegrableOn (fun w : SpaceTime => exp w.1) {w : SpaceTime | w.1 ≤ a} := by
  apply (integrable_stochasticHeatPastWeight a).integrableOn.congr
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_fst measurable_const)] with w hw
  exact indicator_of_mem (show w.1 ∈ Iic a from hw) exp

theorem continuous_massiveHeatKernel_convolution_of_weighted_past
    {g : SpaceTime → ℝ} (hg : Continuous g)
    (hi : ∀ a : ℝ, IntegrableOn (fun w : SpaceTime => exp w.1 * |g w|)
      {w : SpaceTime | w.1 ≤ a}) :
    Continuous (fun z : SpaceTime => ∫ w : SpaceTime, massiveHeatKernel (z - w) * g w) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let a := z.1 - 3
  let b := z.1 + 3
  have hab : a ≤ b := by dsimp [a, b]; linarith
  let g₀ : SpaceTime → ℝ := fun w => g ((projIcc a b hab w.1 : ℝ), w.2)
  have hg₀ : Continuous g₀ := hg.comp
    (((continuous_subtype_val.comp continuous_projIcc).comp continuous_fst).prodMk continuous_snd)
  have hbdd : BddAbove (range fun w : SpaceTime => ‖g₀ w‖) := by
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod
      (isCompact_univ : IsCompact (univ : Set Torus3))).bddAbove_image hg.norm.continuousOn
    refine ⟨B, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact hB ⟨((projIcc a b hab w.1 : ℝ), w.2),
      ⟨(projIcc a b hab w.1).property, mem_univ _⟩, rfl⟩
  obtain ⟨B, hB⟩ := hbdd
  have hg₀B (w : SpaceTime) : |g₀ w| ≤ B := by
    exact (Real.norm_eq_abs (g₀ w)) ▸ hB (mem_range_self w)
  have hlocalInt (p : SpaceTime) : Integrable (fun w : SpaceTime =>
      massiveHeatKernel (p - w) * g₀ w) :=
    (integrable_comp_sub_left_spaceTime integrable_massiveHeatKernel p).mul_bdd
      hg₀.aestronglyMeasurable (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]; exact hg₀B w)
  have hlocalCont : Continuous (fun p : SpaceTime =>
      ∫ w : SpaceTime, massiveHeatKernel (p - w) * g₀ w) := by
    have hbg : BddAbove (range fun w : SpaceTime => ‖g₀ w‖) := ⟨B, hB⟩
    have hc := hbg.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℝ ℝ)
      integrable_massiveHeatKernel hg₀
    convert hc using 1
    funext p
    exact (convolution_eq_swap (L := ContinuousLinearMap.mul ℝ ℝ)
      (f := massiveHeatKernel) (g := g₀) (μ := volume) (x := p)).symm
  let h : SpaceTime → ℝ := fun w => g w - g₀ w
  have hm : Measurable h := hg.measurable.sub hg₀.measurable
  have habs : Measurable (fun w => |h w|) := by
    simpa only [h, Pi.sub_apply, Real.norm_eq_abs] using (hg.sub hg₀).norm.measurable
  have hh : IntegrableOn (fun w : SpaceTime => exp w.1 * |h w|)
      {w : SpaceTime | w.1 ≤ a} := by
    apply ((hi a).add ((exp_past_integrable a).mul_const B)).mono'
      ((measurable_exp.comp measurable_fst).mul habs).aestronglyMeasurable
    filter_upwards [] with w
    change ‖exp w.1 * |h w|‖ ≤ exp w.1 * |g w| + exp w.1 * B
    rw [Real.norm_of_nonneg (mul_nonneg (exp_nonneg _) (abs_nonneg _)), ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
    exact (abs_sub (g w) (g₀ w)).trans (add_le_add_right (hg₀B w) _)
  have htailCont := continuousAt_massiveHeatKernel_past_convolution hm hh
    (z := z) (by dsimp [a]; linarith)
  have hc := hlocalCont.continuousAt.add htailCont
  apply hc.congr
  filter_upwards [continuousAt_fst.preimage_mem_nhds
    (Ioo_mem_nhds (show z.1 - 1 < z.1 by linarith) (show z.1 < z.1 + 1 by linarith))]
    with p hp
  have hp' : z.1 - 1 < p.1 ∧ p.1 < z.1 + 1 := hp
  have htailInt := integrableOn_massiveHeatKernel_past_product hm hh
    (z := p) (by dsimp [a]; linarith only [hp'.1])
  have hset : MeasurableSet {w : SpaceTime | w.1 ≤ a} :=
    measurableSet_le measurable_fst measurable_const
  change (∫ w : SpaceTime, massiveHeatKernel (p - w) * g₀ w) +
    (∫ w in {w : SpaceTime | w.1 ≤ a}, massiveHeatKernel (p - w) * h w) = _
  rw [← integral_indicator hset, ← integral_add (hlocalInt p)
    (htailInt.integrable_indicator hset)]
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : w.1 ≤ a
  · rw [indicator_of_mem (show w ∈ {v : SpaceTime | v.1 ≤ a} from hw)]
    dsimp [h]
    ring
  · rw [indicator_of_notMem (show w ∉ {v : SpaceTime | v.1 ≤ a} from hw), add_zero]
    by_cases hwb : w.1 ≤ b
    · have hmem : w.1 ∈ Icc a b := ⟨(lt_of_not_ge hw).le, hwb⟩
      have he : g₀ w = g w := by
        dsimp [g₀]
        rw [projIcc_of_mem hab hmem]
      rw [he]
    · have htime : ¬0 < (p - w).1 := by
        change ¬0 < p.1 - w.1
        dsimp [b] at hwb
        linarith only [hp'.2, lt_of_not_ge hwb]
      simp only [massiveHeatKernel, htime, ↓reduceIte, zero_mul]

end RegularityStructures.Phi43

end
