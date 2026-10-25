/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Mollifier
public import Phi43.Constants.Finite
public import Phi43.ClassicalSolution.PeriodiseRegularity
public import RegularityStructures.Probability.SpaceTimeMeasure
public import Phi43.Torus.KernelBoundsConvolution
public import Mathlib.Analysis.Convolution

/-!
# An `L²` Young inequality for the smeared test function

For a regularised noise `ξ` at scale `ε` and a test function `ψ` on `ℝ × T³`, the pairing
`∫ ξ ψ` is (almost surely) the white-noise pairing `W g` with
`g(u) = ∫ ψ(w) ρ_ε^♯(w - u) dw`.  This module records the deterministic part: `g` is measurable,
square integrable, and `‖g‖₂ ≤ ‖ρ‖₁ ‖ψ‖₂` uniformly in `ε ∈ (0, 1]`, with no sign assumption on
the mollifier `ρ`.  The proof is the weighted Cauchy-Schwarz inequality followed by Mathlib's
convolution of integrable functions.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The test function `ψ` smeared by the periodised mollifier:
`g(u) = ∫ ψ(w) ρ_ε^♯(w - u) dw`. -/
def noiseSmearedTest (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (ψ : SpaceTime → ℝ)
    (u : SpaceTime) : ℝ :=
  ∫ w, ψ w * periodise ρ ε (w - u)

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- Weighted Cauchy-Schwarz inequality `(∫ f h)² ≤ (∫ h)(∫ f² h)` for a nonnegative weight. -/
theorem noiseIntegral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f h : α → ℝ} (hh0 : ∀ a, 0 ≤ h a) (hh : Integrable h μ)
    (hfh : Integrable (fun a => f a * h a) μ)
    (hf2h : Integrable (fun a => f a ^ 2 * h a) μ) :
    (∫ a, f a * h a ∂μ) ^ 2 ≤ (∫ a, h a ∂μ) * ∫ a, f a ^ 2 * h a ∂μ := by
  have key : ∀ x : ℝ, 0 ≤ (∫ a, f a ^ 2 * h a ∂μ) * (x * x) +
      (-2 * ∫ a, f a * h a ∂μ) * x + ∫ a, h a ∂μ := by
    intro x
    have hA : Integrable (fun a => x ^ 2 * (f a ^ 2 * h a) - 2 * x * (f a * h a)) μ :=
      (hf2h.const_mul (x ^ 2)).sub (hfh.const_mul (2 * x))
    have hint : ∫ a, (x * f a - 1) ^ 2 * h a ∂μ =
        (∫ a, f a ^ 2 * h a ∂μ) * (x * x) + (-2 * ∫ a, f a * h a ∂μ) * x +
          ∫ a, h a ∂μ := by
      rw [show (fun a => (x * f a - 1) ^ 2 * h a) =
          fun a => (x ^ 2 * (f a ^ 2 * h a) - 2 * x * (f a * h a)) + h a by
        funext a
        ring]
      rw [integral_add hA hh, integral_sub (hf2h.const_mul _) (hfh.const_mul _),
        integral_const_mul, integral_const_mul]
      ring
    rw [← hint]
    exact integral_nonneg fun a => mul_nonneg (sq_nonneg _) (hh0 a)
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith

/-- `u ↦ ∫ ψ(w) K(w - u) dw` is measurable. -/
theorem measurable_noiseConv {K ψ : SpaceTime → ℝ} (hK : Measurable K) (hψ : Measurable ψ) :
    Measurable (fun u : SpaceTime => ∫ w, ψ w * K (w - u)) := by
  have hm : Measurable (fun q : SpaceTime × SpaceTime => ψ q.2 * K (q.2 - q.1)) :=
    (hψ.comp measurable_snd).mul (hK.comp (measurable_snd.sub measurable_fst))
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

/-- The `L²` Young inequality `‖∫ ψ(w) K(w - ·) dw‖₂ ≤ ‖K‖₁ ‖ψ‖₂` for a bounded integrable
kernel `K`. -/
theorem noiseConv_sq_integral_le {K ψ : SpaceTime → ℝ} (hK : Measurable K)
    (hKi : Integrable K) {B : ℝ} (hKb : ∀ z, |K z| ≤ B) (hψm : Measurable ψ)
    (hψ : MemLp ψ 2) :
    Integrable (fun u : SpaceTime => (∫ w, ψ w * K (w - u)) ^ 2) ∧
      ∫ u, (∫ w, ψ w * K (w - u)) ^ 2 ≤ (∫ w, |K w|) ^ 2 * ∫ w, ψ w ^ 2 := by
  have hψ2 : Integrable (fun w => ψ w ^ 2) := hψ.integrable_sq
  have hKt : Integrable (fun v : SpaceTime => |K (-v)|) :=
    (hKi.norm.comp_neg : Integrable (fun v : SpaceTime => ‖K (-v)‖))
  set M : ℝ := ∫ w, |K w| with hM
  have hM0 : 0 ≤ M := integral_nonneg fun w => abs_nonneg _
  let F : SpaceTime → ℝ := fun u => ∫ t, ψ t ^ 2 * |K (t - u)|
  have hFconv : F = convolution (fun t => ψ t ^ 2) (fun v : SpaceTime => |K (-v)|)
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext u
    simp only [F, convolution_def, ContinuousLinearMap.mul_apply', neg_sub]
  have hFint : Integrable F := by
    rw [hFconv]
    exact Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hψ2 hKt
  have hFval : ∫ u, F u = (∫ w, ψ w ^ 2) * M := by
    rw [hFconv, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hψ2 hKt]
    simp only [ContinuousLinearMap.mul_apply']
    rw [integral_neg_eq_self (fun v : SpaceTime => |K v|) volume]
  have hpt : ∀ u, (∫ w, ψ w * K (w - u)) ^ 2 ≤ M * F u := by
    intro u
    have hh : Integrable (fun w => |K (w - u)|) := hKi.norm.comp_sub_right u
    have hhval : ∫ w, |K (w - u)| = M := integral_sub_right_eq_self (fun w => |K w|) u
    have hmeasK : Measurable (fun w => |K (w - u)|) :=
      (hK.comp (measurable_id.sub measurable_const)).norm
    have hψa : Measurable (fun w => |ψ w|) := hψm.norm
    have hf2h : Integrable (fun w => |ψ w| ^ 2 * |K (w - u)|) := by
      refine (hψ2.const_mul B).mono' ((hψa.pow_const 2).mul hmeasK).aestronglyMeasurable
        (Filter.Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq_abs]
      calc ψ w ^ 2 * |K (w - u)| ≤ ψ w ^ 2 * B :=
            mul_le_mul_of_nonneg_left (hKb _) (sq_nonneg _)
        _ = B * ψ w ^ 2 := by ring
    have hfh : Integrable (fun w => |ψ w| * |K (w - u)|) := by
      refine ((hf2h.add hh).const_mul (1 / 2 : ℝ)).mono'
        (hψa.mul hmeasK).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [Pi.add_apply]
      have h0 := abs_nonneg (K (w - u))
      nlinarith [sq_nonneg (|ψ w| - 1), mul_nonneg h0 (sq_nonneg (|ψ w| - 1))]
    have hcs := noiseIntegral_mul_sq_le (μ := volume) (f := fun w => |ψ w|)
      (h := fun w => |K (w - u)|) (fun _ => abs_nonneg _) hh hfh hf2h
    rw [hhval] at hcs
    have habs : |∫ w, ψ w * K (w - u)| ≤ ∫ w, |ψ w| * |K (w - u)| := by
      have := norm_integral_le_integral_norm (μ := volume) (fun w => ψ w * K (w - u))
      simpa [abs_mul] using this
    have hsq : (∫ w, ψ w * K (w - u)) ^ 2 ≤ (∫ w, |ψ w| * |K (w - u)|) ^ 2 := by
      rw [← sq_abs (∫ w, ψ w * K (w - u))]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    refine hsq.trans (hcs.trans_eq ?_)
    simp only [F, sq_abs]
  have hgm := measurable_noiseConv hK hψm
  have hint : Integrable (fun u : SpaceTime => (∫ w, ψ w * K (w - u)) ^ 2) := by
    refine (hFint.const_mul M).mono' (hgm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt u
  refine ⟨hint, ?_⟩
  calc ∫ u, (∫ w, ψ w * K (w - u)) ^ 2 ≤ ∫ u, M * F u := integral_mono hint (hFint.const_mul M) hpt
    _ = M * ((∫ w, ψ w ^ 2) * M) := by rw [integral_const_mul, hFval]
    _ = M ^ 2 * ∫ w, ψ w ^ 2 := by ring

/-- The `L¹` norm of the periodised mollifier is at most that of `ρ`. -/
theorem integral_abs_periodise_le_integral_abs {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) :
    ∫ z : SpaceTime, |periodise ρ ε z| ≤ ∫ z : ParabolicSpace, |ρ z| := by
  refine (integral_abs_periodise_le ρ hρ hε.1 hε.2).trans_eq ?_
  exact integral_abs_rescale ρ hε.1

/-- **Young bound for the smeared test function**, uniform in `ε ∈ (0, 1]` and without a sign
condition on `ρ`. -/
theorem noiseSmearedTest_sq_integral_le {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) {ψ : SpaceTime → ℝ} (hψm : Measurable ψ)
    (hψ : MemLp ψ 2) :
    MemLp (noiseSmearedTest ρ ε ψ) 2 ∧
      ∫ u, noiseSmearedTest ρ ε ψ u ^ 2 ≤ (∫ z : ParabolicSpace, |ρ z|) ^ 2 * ∫ w, ψ w ^ 2 := by
  obtain ⟨B, hB⟩ := bounded_periodise ρ hρ hε.1
  have hK := measurable_periodise ρ hρ (ε := ε)
  obtain ⟨hint, hle⟩ := noiseConv_sq_integral_le hK (integrable_periodise ρ hρ hε.1) hB hψm hψ
  have hgm : Measurable (noiseSmearedTest ρ ε ψ) := measurable_noiseConv hK hψm
  refine ⟨?_, ?_⟩
  · refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 ?_
    exact hint
  · refine hle.trans ?_
    have hM := integral_abs_periodise_le_integral_abs hρ hε
    have hM0 : 0 ≤ ∫ w : SpaceTime, |periodise ρ ε w| := integral_nonneg fun w => abs_nonneg _
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM0 hM 2)
      (integral_nonneg fun w => sq_nonneg _)

end RegularityStructures.Phi43

end
