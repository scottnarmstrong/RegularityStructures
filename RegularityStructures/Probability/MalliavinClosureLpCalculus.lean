/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureCalculus
public import Mathlib.MeasureTheory.Function.UnifTight

/-!
# L² convergence under bounded multipliers

The closure-level chain and product rules use the elementary Vitali argument that a bounded
multiplier converging almost everywhere can be multiplied into an `L²` function.  This module
records that argument with no hidden integrability assumptions.  The bound is stated against one
fixed `L²` majorant, which supplies both uniform integrability and uniform tightness.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace RegularityStructures

theorem tendsto_Lp_zero_of_ae_tendsto_bounded_by
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : MemLp g 2 μ)
    (hbound : ∃ c : ℝ≥0, ∀ n, ∀ᵐ x ∂μ,
      ‖f n x‖ₑ ≤ ‖(c : ℝ) * g x‖ₑ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := hbound
  have hmajor : MemLp (fun x => (c : ℝ) * g x) 2 μ := hg.const_mul c
  have hui_major : UnifIntegrable (fun _ : ℕ => (fun x => (c : ℝ) * g x)) 2 μ :=
    (uniformIntegrable_const (p := (2 : ℝ≥0∞)) (μ := μ) (ι := ℕ)
      (by norm_num) (by norm_num) hmajor).unifIntegrable
  have hui : UnifIntegrable f 2 μ := by
    apply hui_major.ae_mono hfm
    intro n
    exact hc n
  have hut_major : UnifTight (fun _ : ℕ => (fun x => (c : ℝ) * g x)) 2 μ :=
    unifTight_const (p := (2 : ℝ≥0∞)) (μ := μ) (ι := ℕ) (by norm_num) hmajor
  have hut : UnifTight f 2 μ := by
    intro ε hε
    obtain ⟨s, hs, hsf, hmajor_s⟩ := hut_major.exists_measurableSet_indicator hε.ne'
    refine ⟨s, ne_of_lt hsf, fun n => ?_⟩
    refine (eLpNorm_mono_enorm_ae (hfm n |>.indicator hs.compl) ?_).trans (hmajor_s n)
    filter_upwards [hc n] with x hx
    by_cases hxs : x ∈ sᶜ
    · simpa [Set.indicator_of_mem hxs] using hx
    · simp [Set.indicator_of_notMem hxs]
  simpa using
    (tendsto_Lp_of_tendsto_ae (p := (2 : ℝ≥0∞)) (μ := μ)
      (by norm_num) (by norm_num) hfm MemLp.zero hui hut hlim)

end RegularityStructures

end
