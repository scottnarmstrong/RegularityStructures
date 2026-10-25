/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.LinearSums
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Identifying a Fourier series with white noise

This module separates the `L²` identification from the deterministic smoothness estimate.  Finite
white-noise linearity identifies every finite Fourier partial sum with the corresponding evaluation
of its finite kernel.  If those partial sums converge in `L²(P)` to `W h`, while they converge
pointwise almost everywhere to the candidate series, uniqueness of limits in measure identifies the
candidate series with `W h` almost surely.
-/

@[expose] public section

open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace RegularityStructures.Phi43

theorem whiteNoise_ae_eq_tsum_of_tendsto_Lp
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (s : ℕ → Finset ι) (a : ι → ℝ) (e : ι → SpaceTime → ℝ)
    {h : SpaceTime → ℝ}
    (hnoise : MemLp (fun w => W h w) 2 P)
    (he : ∀ i, MemLp (e i) 2 (volume : Measure SpaceTime))
    (hkernel : ∀ n, MemLp (∑ i ∈ s n, a i • e i) 2
      (volume : Measure SpaceTime))
    (hpartial : ∀ n, MemLp (fun w => ∑ i ∈ s n, a i * W (e i) w) 2 P)
    (hLp : Tendsto
      (fun n =>
        ((hW.2 1 (fun _ => ∑ i ∈ s n, a i • e i) (fun _ => hkernel n)).memLp_two_apply 0).toLp
          (fun w => W (∑ i ∈ s n, a i • e i) w))
      atTop (𝓝 (hnoise.toLp (fun w => W h w))))
    (hseries : ∀ᵐ w ∂P,
      Tendsto (fun n => ∑ i ∈ s n, a i * W (e i) w) atTop
        (𝓝 (∑' i, a i * W (e i) w))) :
    (fun w => ∑' i, a i * W (e i) w) =ᵐ[P] fun w => W h w := by
  have hfinite : ∀ n,
      (fun w => ∑ i ∈ s n, a i * W (e i) w) =ᵐ[P]
        (fun w => W (∑ i ∈ s n, a i • e i) w) := by
    intro n
    exact (whiteNoise_finset_sum_ae hW (s n) a e (fun i _ => he i)).symm
  have hkernelNoise : ∀ n, MemLp
      (fun w => W (∑ i ∈ s n, a i • e i) w) 2 P := by
    intro n
    exact (hW.2 1 (fun _ => ∑ i ∈ s n, a i • e i) (fun _ => hkernel n)).memLp_two_apply 0
  have hLpMeasure : TendstoInMeasure P
      (fun n w => ∑ i ∈ s n, a i * W (e i) w) atTop (fun w => W h w) := by
    have h0 := tendstoInMeasure_of_tendsto_Lp hLp
    have h1 := h0.congr_left (fun n =>
      ((hkernelNoise n).coeFn_toLp.trans (hfinite n).symm))
    exact h1.congr_right hnoise.coeFn_toLp
  have hSeriesMeasure : TendstoInMeasure P
      (fun n w => ∑ i ∈ s n, a i * W (e i) w) atTop
        (fun w => ∑' i, a i * W (e i) w) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (hpartial n).aestronglyMeasurable
    · exact hseries
  exact tendstoInMeasure_ae_unique hSeriesMeasure hLpMeasure

end RegularityStructures.Phi43

end
