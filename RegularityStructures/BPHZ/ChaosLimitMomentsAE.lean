/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.WhiteNoiseChaosMoments

/-!
# Moment equivalence for almost sure limits of finite-chaos random variables

If `Rₖ` are (almost surely) cylindrical polynomials of degree at most `m` of a white noise,
`Rₖ → X` almost surely and `sup_k E Rₖ² < ∞`, then `E X^(2p) ≤ A * (E X²)^p`, with the constant
`A = A(m, p)` of `integral_pow_two_mul_le_of_tendsto_cylindricalPolynomial`.

The proof upgrades almost sure convergence to `L²` convergence: hypercontractivity bounds
`E Rₖ⁴`, hence `E (Rₖ - X)⁴`, and an almost surely convergent sequence bounded in `L⁴` converges
in `L²` (`tendsto_integral_sq_of_ae_tendsto_of_integral_pow_four_le`, by truncation at a level
`M`: the truncated part converges by dominated convergence and the tail is at most `D / (4 M)`).
-/

public section

open MvPolynomial MeasureTheory Filter Topology

namespace RegularityStructures

universe u

/-- Elementary truncation inequality: `z² ≤ min z² M + z⁴ / (4 M)` for `M > 0`. -/
private lemma sq_le_min_add_pow_four_div (z M : ℝ) (hM : 0 < M) :
    z ^ 2 ≤ min (z ^ 2) M + z ^ 4 / (4 * M) := by
  have h4 : 0 ≤ z ^ 4 / (4 * M) := by positivity
  rcases le_total (z ^ 2) M with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    have : z ^ 2 - M ≤ z ^ 4 / (4 * M) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (z ^ 2 - 2 * M)]
    linarith

/-- An almost surely convergent sequence that is bounded in `L⁴` of a probability space
converges to zero in `L²`. -/
theorem tendsto_integral_sq_of_ae_tendsto_of_integral_pow_four_le {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : ℕ → Ω → ℝ} {D : ℝ}
    (hmeas : ∀ k, AEStronglyMeasurable (Z k) μ)
    (hint4 : ∀ k, Integrable (fun ω => Z k ω ^ 4) μ)
    (hD : ∀ k, ∫ ω, Z k ω ^ 4 ∂μ ≤ D)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => Z k ω) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, Z k ω ^ 2 ∂μ) atTop (𝓝 0) := by
  have hD0 : 0 ≤ D := (integral_nonneg fun ω => by positivity).trans (hD 0)
  have hint2 : ∀ k, Integrable (fun ω => Z k ω ^ 2) μ := fun k => by
    refine Integrable.mono' ((hint4 k).add (integrable_const (1 : ℝ)))
      ((hmeas k).pow 2) (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, norm_pow, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (Z k ω ^ 2 - 1), sq_nonneg (Z k ω)]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℝ := (D + 1) / ε with hMdef
  have hM : 0 < M := by positivity
  have hMtail : D / (4 * M) < ε / 2 := by
    rw [div_lt_iff₀ (by positivity), hMdef]
    have : (D + 1) / ε * ε = D + 1 := div_mul_cancel₀ _ hε.ne'
    nlinarith
  have hconv : Tendsto (fun k => ∫ ω, min (Z k ω ^ 2) M ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun k ω => min (Z k ω ^ 2) M) (f := fun _ => (0 : ℝ)) (fun _ => M)
      (fun k => ((hmeas k).pow 2).inf aestronglyMeasurable_const)
      (integrable_const M)
      (fun k => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) hM.le)]
        exact min_le_right _ _)
      (by
        filter_upwards [hlim] with ω hω
        have h2 : Tendsto (fun k => Z k ω ^ 2) atTop (𝓝 0) := by
          simpa using hω.pow 2
        have := h2.min (tendsto_const_nhds (x := M))
        simpa [min_eq_left hM.le] using this)
    simpa using h
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hconv) (ε / 2) (by positivity)
  refine ⟨K, fun k hk => ?_⟩
  have h1 := hK k hk
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  have hmin : Integrable (fun ω => min (Z k ω ^ 2) M) μ :=
    ((hint2 k).inf (integrable_const M))
  have hle : ∫ ω, Z k ω ^ 2 ∂μ ≤
      ∫ ω, min (Z k ω ^ 2) M ∂μ + ∫ ω, Z k ω ^ 4 / (4 * M) ∂μ := by
    rw [← integral_add hmin ((hint4 k).div_const _)]
    exact integral_mono (hint2 k) (hmin.add ((hint4 k).div_const _)) fun ω =>
      sq_le_min_add_pow_four_div _ _ hM
  have hnn : 0 ≤ ∫ ω, Z k ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have htail : ∫ ω, Z k ω ^ 4 / (4 * M) ∂μ ≤ D / (4 * M) := by
    rw [integral_div]
    exact div_le_div_of_nonneg_right (hD k) (by positivity)
  rw [abs_of_nonneg hnn]
  have := (le_abs_self _).trans_lt h1
  linarith

end RegularityStructures

end
