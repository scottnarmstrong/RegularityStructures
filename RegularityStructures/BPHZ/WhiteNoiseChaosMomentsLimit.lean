/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Limits of `L²`-convergent sequences: Fatou and norm convergence

Two measure-theoretic ingredients for passing moment bounds to `L²` limits:

* `integrable_and_integral_le_of_ae_tendsto`: Fatou's lemma for a.e. convergent nonnegative
  measurable functions whose integrals are bounded by a convergent real sequence;
* `tendsto_integral_sq_of_tendsto_integral_sq_sub` and
  `exists_strictMono_ae_tendsto_of_tendsto_integral_sq_sub`: if `∫ (Fₖ - F)² → 0` for square
  integrable `Fₖ`, `F`, then `∫ Fₖ² → ∫ F²` and a subsequence converges a.e.
-/

public section

open MeasureTheory Filter Topology

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Fatou's lemma** for nonnegative measurable functions with a.e. limit `G` and integrals
bounded by a convergent real sequence: the limit is integrable and its integral is bounded by
the limit of the bounds. -/
theorem integrable_and_integral_le_of_ae_tendsto {G : ℕ → Ω → ℝ} {G' : Ω → ℝ} {b : ℕ → ℝ}
    {B : ℝ} (hmeas : ∀ k, Measurable (G k)) (hnn : ∀ k ω, 0 ≤ G k ω)
    (hint : ∀ k, Integrable (G k) μ) (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => G k ω) atTop (𝓝 (G' ω)))
    (hb : ∀ k, ∫ ω, G k ω ∂μ ≤ b k) (hbB : Tendsto b atTop (𝓝 B)) :
    Integrable G' μ ∧ ∫ ω, G' ω ∂μ ≤ B := by
  have hB : 0 ≤ B := ge_of_tendsto hbB (Eventually.of_forall fun k =>
    (integral_nonneg (hnn k)).trans (hb k))
  have hmeas' : AEMeasurable G' μ :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun k => (hmeas k).aemeasurable) hlim
  have hnn' : 0 ≤ᵐ[μ] G' := by
    filter_upwards [hlim] with ω hω using ge_of_tendsto' hω fun k => hnn k ω
  have hl : ∫⁻ ω, ENNReal.ofReal (G' ω) ∂μ ≤ ENNReal.ofReal B := by
    calc ∫⁻ ω, ENNReal.ofReal (G' ω) ∂μ
        = ∫⁻ ω, liminf (fun k => ENNReal.ofReal (G k ω)) atTop ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim] with ω hω
          exact ((ENNReal.tendsto_ofReal hω).liminf_eq).symm
      _ ≤ liminf (fun k => ∫⁻ ω, ENNReal.ofReal (G k ω) ∂μ) atTop :=
          lintegral_liminf_le fun k => ENNReal.measurable_ofReal.comp (hmeas k)
      _ ≤ liminf (fun k => ENNReal.ofReal (b k)) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hint k) (Eventually.of_forall (hnn k))]
          exact ENNReal.ofReal_le_ofReal (hb k)
      _ = ENNReal.ofReal B := (ENNReal.tendsto_ofReal hbB).liminf_eq
  have hfin : Integrable G' μ := by
    refine (lintegral_ofReal_ne_top_iff_integrable hmeas'.aestronglyMeasurable hnn').1 ?_
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hl
  refine ⟨hfin, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn' hmeas'.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB hl

/-- For a square integrable `f`, `∫ f² = (‖f‖_{L²})²`. -/
theorem integral_sq_eq_eLpNorm_two_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ∫ ω, f ω ^ 2 ∂μ = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun ω => by positivity) _)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun ω => by positivity)]
  norm_num

/-- The `L²` norm is continuous with respect to `L²` convergence. -/
theorem tendsto_eLpNorm_two_toReal {F : ℕ → Ω → ℝ} {G : Ω → ℝ} (hF : ∀ k, MemLp (F k) 2 μ)
    (hG : MemLp G 2 μ) (hlim : Tendsto (fun k => (eLpNorm (F k - G) 2 μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun k => (eLpNorm (F k) 2 μ).toReal) atTop (𝓝 (eLpNorm G 2 μ).toReal) := by
  have key : ∀ k, |(eLpNorm (F k) 2 μ).toReal - (eLpNorm G 2 μ).toReal| ≤
      (eLpNorm (F k - G) 2 μ).toReal := by
    intro k
    have h1 := abs_norm_sub_norm_le ((hF k).toLp (F k)) (hG.toLp G)
    rw [← MemLp.toLp_sub, Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp] at h1
    exact h1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) key hlim

private lemma tendsto_eLpNorm_sub_toReal {F : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hF : ∀ k, MemLp (F k) 2 μ) (hG : MemLp G 2 μ)
    (hlim : Tendsto (fun k => ∫ ω, (F k ω - G ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => (eLpNorm (F k - G) 2 μ).toReal) atTop (𝓝 0) := by
  have h2 : ∀ k, (eLpNorm (F k - G) 2 μ).toReal = Real.sqrt (∫ ω, (F k ω - G ω) ^ 2 ∂μ) := by
    intro k
    rw [← Real.sqrt_sq ENNReal.toReal_nonneg, ← integral_sq_eq_eLpNorm_two_sq ((hF k).sub hG)]
    rfl
  simp_rw [h2]
  have := (Real.continuous_sqrt.tendsto 0).comp hlim
  simpa [Function.comp_def] using this

/-- If `Fₖ, F` are square integrable and `∫ (Fₖ - F)² → 0`, then `∫ Fₖ² → ∫ F²`. -/
theorem tendsto_integral_sq_of_tendsto_integral_sq_sub {F : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hF : ∀ k, MemLp (F k) 2 μ) (hG : MemLp G 2 μ)
    (hlim : Tendsto (fun k => ∫ ω, (F k ω - G ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, F k ω ^ 2 ∂μ) atTop (𝓝 (∫ ω, G ω ^ 2 ∂μ)) := by
  have := (tendsto_eLpNorm_two_toReal hF hG (tendsto_eLpNorm_sub_toReal hF hG hlim)).pow 2
  simp_rw [← integral_sq_eq_eLpNorm_two_sq (hF _)] at this
  rwa [← integral_sq_eq_eLpNorm_two_sq hG] at this

/-- If `Fₖ, F` are square integrable and `∫ (Fₖ - F)² → 0`, then a subsequence of `Fₖ` converges
to `F` almost everywhere. -/
theorem exists_strictMono_ae_tendsto_of_tendsto_integral_sq_sub {F : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hF : ∀ k, MemLp (F k) 2 μ) (hG : MemLp G 2 μ)
    (hlim : Tendsto (fun k => ∫ ω, (F k ω - G ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂μ, Tendsto (fun i => F (ns i) ω) atTop (𝓝 (G ω)) := by
  have h1 := tendsto_eLpNorm_sub_toReal hF hG hlim
  have h3 : Tendsto (fun k => eLpNorm (F k - G) 2 μ) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_ofReal h1)
    simp only [ENNReal.ofReal_zero] at this
    refine this.congr fun k => ?_
    exact ENNReal.ofReal_toReal ((hF k).sub hG).eLpNorm_ne_top
  exact (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) h3).exists_seq_tendsto_ae

end RegularityStructures

end
