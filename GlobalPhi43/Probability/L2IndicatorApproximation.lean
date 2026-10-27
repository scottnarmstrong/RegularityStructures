/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Probability.WhiteNoiseL2Continuity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Dominated L2 convergence of actual indicator cutoffs. The dominating square
is integrable on the possibly infinite underlying measure space. -/

public noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace GlobalPhi43.Probability

theorem real_toLp_sub_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ z, (f z - g z) ^ 2 ∂μ := by
  have he : (fun z => (hf.toLp f - hg.toLp g) z) =ᵐ[μ] (fun z => f z - g z) :=
    (Lp.coeFn_sub _ _).trans (hf.coeFn_toLp.sub hg.coeFn_toLp)
  rw [realLp_norm_sq]
  exact integral_congr_ae (he.mono fun _ h => congrArg (fun v => v ^ 2) h)

theorem indicator_toLp_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} (hh : MemLp h 2 μ) (S : ℕ → Set α) (hS : ∀ n, MeasurableSet (S n))
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun n => (S n).indicator h z) atTop (𝓝 (h z))) :
    Tendsto (fun n => (hh.indicator (hS n)).toLp ((S n).indicator h)) atTop (𝓝 (hh.toLp h)) := by
  have hbound (n : ℕ) (z : α) : ‖((S n).indicator h z - h z) ^ 2‖ ≤ h z ^ 2 := by
    by_cases hz : z ∈ S n
    · rw [Set.indicator_of_mem hz, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), norm_zero]
      exact sq_nonneg _
    · rw [Set.indicator_of_notMem hz, zero_sub, neg_sq, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
  have hpoint : ∀ᵐ z ∂μ, Tendsto (fun n => ((S n).indicator h z - h z) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hlim] with z hz
    simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (hz.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => h z) atTop (𝓝 (h z)))).pow 2
  have hint := tendsto_integral_of_dominated_convergence (fun z => h z ^ 2)
    (fun n => (((hh.indicator (hS n)).sub hh).integrable_sq).aestronglyMeasurable)
    hh.integrable_sq (fun n => ae_of_all _ (hbound n)) hpoint
  simp only [integral_zero] at hint
  have hn (n : ℕ) :
      ‖(hh.indicator (hS n)).toLp ((S n).indicator h) - hh.toLp h‖ ^ 2 =
        ∫ z, ((S n).indicator h z - h z) ^ 2 ∂μ :=
    real_toLp_sub_norm_sq (hh.indicator (hS n)) hh
  have hsq : Tendsto (fun n =>
      ‖(hh.indicator (hS n)).toLp ((S n).indicator h) - hh.toLp h‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hn, Pi.sub_apply] using hint
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

end GlobalPhi43.Probability
