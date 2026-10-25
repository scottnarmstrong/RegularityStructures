/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Markov, tightness and Cauchy in probability for outer measures

Generic probability lemmas for a probability space `(Ω, P)` and `ℝ≥0∞`-valued functionals
`D : ℝ → ℝ → Ω → ℝ≥0∞` (distances) and `S : ℝ → Ω → ℝ≥0∞` (sizes).  The events
`{ω | ofReal δ < D ε ε' ω}` are only controlled through the outer measure `P`, so moment
bounds are phrased for an `AEMeasurable` majorant.

A majorant cannot be dispensed with: Mathlib's `lintegral` of a non-measurable function is a
supremum over simple minorants, so it can vanish while the function is positive on a set of
positive outer measure.

* `measure_lt_le_lintegral_rpow_div`: Markov for outer measures;
* `tendsto_measure_lt_cauchy_of_lintegral_rpow_le`: Cauchy in probability;
* `exists_measure_lt_le_of_lintegral_rpow_le`: tightness.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Markov's inequality for the outer measure of `{ofReal δ < D}`, with an a.e. measurable
majorant `D'` of `D`. -/
theorem measure_lt_le_lintegral_rpow_div {D D' : Ω → ℝ≥0∞} (hDD' : D ≤ᵐ[P] D')
    (hD' : AEMeasurable D' P) {p δ : ℝ} (hp : 0 < p) (hδ : 0 < δ) :
    P {ω | ENNReal.ofReal δ < D ω} ≤
      (∫⁻ ω, D' ω ^ p ∂P) / ENNReal.ofReal δ ^ p := by
  have hδp : ENNReal.ofReal δ ^ p ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hδ) ENNReal.ofReal_ne_top).ne'
  have hδt : ENNReal.ofReal δ ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
  refine (measure_mono_ae ?_).trans
    (meas_ge_le_lintegral_div (hD'.pow_const p) hδp hδt)
  filter_upwards [hDD'] with ω hω hmem
  exact ENNReal.rpow_le_rpow (hmem.le.trans hω) hp.le

/-- Markov's inequality with a moment bound `∫⁻ D'^p ≤ c`. -/
theorem measure_lt_le_div_of_lintegral_rpow_le {D D' : Ω → ℝ≥0∞} (hDD' : D ≤ᵐ[P] D')
    (hD' : AEMeasurable D' P) {p δ : ℝ} (hp : 0 < p) (hδ : 0 < δ) {c : ℝ≥0∞}
    (hc : ∫⁻ ω, D' ω ^ p ∂P ≤ c) :
    P {ω | ENNReal.ofReal δ < D ω} ≤ c / ENNReal.ofReal δ ^ p :=
  (measure_lt_le_lintegral_rpow_div hDD' hD' hp hδ).trans (by gcongr)

/-- **Cauchy in probability.**  If the `p`-th moments of an a.e. measurable majorant `D'` of the
distance `D ε ε'` are bounded by `C * (max ε ε') ^ (θ * p)` for `ε, ε' ∈ (0, 1]`, then
`P {δ < D ε ε'}` tends to `0` as `(ε, ε') → (0⁺, 0⁺)`. -/
theorem tendsto_measure_lt_cauchy_of_lintegral_rpow_le {D D' : ℝ → ℝ → Ω → ℝ≥0∞}
    {θ p C : ℝ} (hθ : 0 < θ) (hp : 0 < p)
    (hDD' : ∀ ε ε', 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → D ε ε' ≤ᵐ[P] D' ε ε')
    (hmeas : ∀ ε ε', 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → AEMeasurable (D' ε ε') P)
    (hmom : ∀ ε ε', 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∫⁻ ω, D' ε ε' ω ^ p ∂P ≤ ENNReal.ofReal C * ENNReal.ofReal (max ε ε') ^ (θ * p))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun e : ℝ × ℝ => P {ω | ENNReal.ofReal δ < D e.1 e.2 ω})
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hδt : ENNReal.ofReal δ ^ p ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hδ) ENNReal.ofReal_ne_top).ne'
  have h1 : Tendsto (fun e : ℝ × ℝ => ENNReal.ofReal (max e.1 e.2) ^ (θ * p))
      (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 0) := by
    have hc : Continuous fun e : ℝ × ℝ => ENNReal.ofReal (max e.1 e.2) ^ (θ * p) :=
      ENNReal.continuous_rpow_const.comp
        (ENNReal.continuous_ofReal.comp (continuous_fst.max continuous_snd))
    simpa [ENNReal.zero_rpow_of_pos (mul_pos hθ hp)] using hc.tendsto ((0 : ℝ), (0 : ℝ))
  have h2 : Tendsto (fun e : ℝ × ℝ => ENNReal.ofReal C *
      ENNReal.ofReal (max e.1 e.2) ^ (θ * p) * (ENNReal.ofReal δ ^ p)⁻¹)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h3 := ENNReal.Tendsto.mul_const
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) h1 (Or.inr ENNReal.ofReal_ne_top))
      (Or.inr (ENNReal.inv_ne_top.2 hδt))
    simp only [mul_zero, zero_mul] at h3
    refine h3.mono_left ?_
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall fun _ => bot_le) ?_
  have hI : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ x ≤ 1 :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) fun x hx => ⟨hx.1, hx.2.le⟩
  have hev1 : ∀ᶠ e : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ), 0 < e.1 ∧ e.1 ≤ 1 :=
    tendsto_fst.eventually hI
  have hev2 : ∀ᶠ e : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ), 0 < e.2 ∧ e.2 ≤ 1 :=
    tendsto_snd.eventually hI
  filter_upwards [hev1, hev2] with e h1e h2e
  have := measure_lt_le_div_of_lintegral_rpow_le (hDD' e.1 e.2 h1e.1 h1e.2 h2e.1 h2e.2)
    (hmeas e.1 e.2 h1e.1 h1e.2 h2e.1 h2e.2) hp hδ (hmom e.1 e.2 h1e.1 h1e.2 h2e.1 h2e.2)
  simpa [div_eq_mul_inv] using this

/-- **Tightness.**  If an a.e. measurable majorant `S'` of the size `S ε` has `p`-th moment at most
`C` for `ε ∈ (0, 1]`, then for every `ϑ > 0` there is `B` with `P {B < S ε} ≤ ϑ` for all
`ε ∈ (0, 1]`. -/
theorem exists_measure_lt_le_of_lintegral_rpow_le {S S' : ℝ → Ω → ℝ≥0∞} {p C : ℝ} (hp : 0 < p)
    (hSS' : ∀ ε, 0 < ε → ε ≤ 1 → S ε ≤ᵐ[P] S' ε)
    (hmeas : ∀ ε, 0 < ε → ε ≤ 1 → AEMeasurable (S' ε) P)
    (hmom : ∀ ε, 0 < ε → ε ≤ 1 → ∫⁻ ω, S' ε ω ^ p ∂P ≤ ENNReal.ofReal C)
    {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∃ B : ℝ, ∀ ε, 0 < ε → ε ≤ 1 → P {ω | ENNReal.ofReal B < S ε ω} ≤ ENNReal.ofReal ϑ := by
  set B : ℝ := (max C 0 / ϑ + 1) ^ (1 / p) with hB
  have hpos : 0 < max C 0 / ϑ + 1 := by positivity
  have hBpos : 0 < B := Real.rpow_pos_of_pos hpos _
  have hBp : B ^ p = max C 0 / ϑ + 1 := by
    rw [hB, ← Real.rpow_mul hpos.le, one_div_mul_cancel hp.ne', Real.rpow_one]
  refine ⟨B, fun ε h0 h1 => ?_⟩
  refine (measure_lt_le_div_of_lintegral_rpow_le (hSS' ε h0 h1) (hmeas ε h0 h1) hp hBpos
    (hmom ε h0 h1)).trans ?_
  rw [ENNReal.ofReal_rpow_of_pos hBpos, hBp,
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hpos, mul_add, mul_div_cancel₀ _ hϑ.ne']
  linarith [le_max_left C 0]

end RegularityStructures
