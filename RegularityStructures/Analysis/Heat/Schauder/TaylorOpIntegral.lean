/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorOp
public import RegularityStructures.Analysis.Heat.Schauder.TaylorGen
public import RegularityStructures.Analysis.Heat.Schauder.TaylorGenerator
public import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Integrals of shifted functions

`∫_w ∫_{t ∈ [0,1]} |g(w + t u)| = ∫ |g|` (`integral_integral_abs_shift`) and the `L¹` bound on the
Taylor remainder operator (`integral_abs_remOp_le`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem integrable_abs_shift_prod {g : ParabolicSpace → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) (u : ParabolicSpace) :
    Integrable (fun p : ParabolicSpace × ℝ => |g (p.1 + p.2 • u)|)
      (volume.prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  have hr : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w, g (w + t • u) ≠ 0 →
      w ∈ Metric.cthickening ‖u‖ (tsupport g) := by
    intro t ht w hw
    have hmem : w + t • u ∈ tsupport g := subset_tsupport g hw
    refine Metric.mem_cthickening_of_dist_le w (w + t • u) ‖u‖ (tsupport g) hmem ?_
    rw [dist_eq_norm]
    have : w - (w + t • u) = -(t • u) := by abel
    rw [this, norm_neg, norm_smul, Real.norm_of_nonneg ht.1]
    nlinarith [ht.2, norm_nonneg u]
  set K' := Metric.cthickening ‖u‖ (tsupport g) with hK'
  have hKc : IsCompact K' := hc.isCompact.cthickening
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  have hmeasK : MeasurableSet K' := hKc.isClosed.measurableSet
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hν
  have hνfin : IsFiniteMeasure ν := ⟨by simp [hν]⟩
  have hint : Integrable (fun p : ParabolicSpace × ℝ => |g (p.1 + p.2 • u)|)
      (volume.prod ν) := by
    have hmaj : Integrable (fun p : ParabolicSpace × ℝ =>
        (K'.indicator (fun _ => B) p.1) * (1 : ℝ)) (volume.prod ν) := by
      refine Integrable.mul_prod (f := K'.indicator (fun _ => B)) (g := fun _ : ℝ => (1 : ℝ)) ?_ ?_
      · exact (integrable_indicator_iff hmeasK).2 (integrableOn_const hKc.measure_lt_top.ne)
      · exact integrable_const _
    refine hmaj.mono' ?_ ?_
    · exact (hg.comp (by fun_prop)).abs.aestronglyMeasurable
    · have hae : ∀ᵐ p ∂(volume.prod ν), p.2 ∈ Icc (0 : ℝ) 1 :=
        (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ParabolicSpace)) (ν := ν)).ae
          (ae_restrict_mem measurableSet_Icc)
      filter_upwards [hae] with p hp
      rw [Real.norm_eq_abs, abs_abs, mul_one]
      by_cases h0 : g (p.1 + p.2 • u) = 0
      · rw [h0, abs_zero]
        exact Set.indicator_nonneg (fun _ _ => (abs_nonneg _).trans (by simpa using hB 0)) _
      · rw [Set.indicator_of_mem (hr p.2 hp p.1 h0)]
        simpa using hB (p.1 + p.2 • u)
  exact hint

/-- Minkowski: `∫_w ∫_{t ∈ [0,1]} |g(w + t u)| = ∫ |g|` for compactly supported continuous `g`. -/
theorem integral_integral_abs_shift {g : ParabolicSpace → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) (u : ParabolicSpace) :
    ∫ w, ∫ t in (0 : ℝ)..1, |g (w + t • u)| = ∫ w, |g w| := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hν
  have hint := integrable_abs_shift_prod hg hc u
  have hswap := integral_integral_swap (μ := (volume : Measure ParabolicSpace)) (ν := ν)
    (f := fun w t => |g (w + t • u)|) hint
  have e1 : ∀ w : ParabolicSpace, ∫ t in (0 : ℝ)..1, |g (w + t • u)| =
      ∫ t, |g (w + t • u)| ∂ν := fun w => by
    rw [intervalIntegral.integral_of_le zero_le_one, hν, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  simp_rw [e1]
  rw [hswap]
  have : (volume : Measure ParabolicSpace).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  have e2 : ∀ t : ℝ, ∫ w, |g (w + t • u)| = ∫ w, |g w| := fun t =>
    integral_add_right_eq_self (fun w => |g w|) (t • u)
  simp_rw [e2]
  rw [integral_const, hν]
  simp

theorem integrable_integral_abs_shift {g : ParabolicSpace → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) (u : ParabolicSpace) :
    Integrable fun w : ParabolicSpace => ∫ t in (0 : ℝ)..1, |g (w + t • u)| := by
  have hint := integrable_abs_shift_prod hg hc u
  have := hint.integral_prod_left
  refine this.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [intervalIntegral.integral_of_le zero_le_one, Measure.restrict_congr_set Ioc_ae_eq_Icc]

theorem integral_abs_remOp_le {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (e : ParabolicSpace) (s : ℝ) (m : ℕ) :
    ∫ w, |remOp e s m φ w| ≤ |s| ^ (m + 1) * ∫ w, |(dirDeriv e)^[m + 1] φ w| := by
  set g := (dirDeriv e)^[m + 1] φ with hg
  have hgc : Continuous g := (contDiff_iterate_dirDeriv hφ e (m + 1)).continuous
  have hgs : HasCompactSupport g := hasCompactSupport_iterate_dirDeriv hc e (m + 1)
  have hI := integrable_integral_abs_shift hgc hgs (s • e)
  have e1 : ∀ w : ParabolicSpace, ∫ t in (0 : ℝ)..1, |g (w + (t * s) • e)| =
      ∫ t in (0 : ℝ)..1, |g (w + t • (s • e))| := fun w => by simp only [mul_smul]
  calc ∫ w, |remOp e s m φ w| ≤ ∫ w, |s| ^ (m + 1) * ∫ t in (0 : ℝ)..1, |g (w + t • (s • e))| := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => abs_nonneg _)
          (hI.const_mul _) (Filter.Eventually.of_forall fun w => ?_)
        beta_reduce
        rw [← e1]
        exact abs_remOp_le hφ e s m w
    _ = _ := by rw [integral_const_mul, integral_integral_abs_shift hgc hgs]

end RegularityStructures

end
