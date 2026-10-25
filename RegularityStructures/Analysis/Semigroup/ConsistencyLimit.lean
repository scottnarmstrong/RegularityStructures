/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Consistency
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic
public import RegularityStructures.Analysis.Semigroup.Pairing.LocalOrder
public import RegularityStructures.Abstract.Examples
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The semigroup as an approximate identity

`tendsto_apply_nhdsGT`: `Q_s g (x) → g (x)` as `s ↓ 0` for `g` bounded measurable and continuous at
`x`, from the quantitative estimate `abs_apply_sub_le`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

end RegularityStructures.RegularisingSemigroup

end

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- Pointwise estimate behind the approximate identity: if `|g| ≤ B` and `|g y - g x| < ε` when
`d(y, x) < δ`, then `|Q_s g (x) - g x| ≤ ε M₀ + 2 B δ⁻¹ M₁ s^{1/ℓ}`. -/
theorem abs_apply_sub_le (hK : K.IsConservative) {s : ℝ} (hs : 0 < s) {g : E → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) (x : E) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hc : ∀ y, K.scaleDist y x < δ → |g y - g x| < ε) :
    |K.apply s g x - g x| ≤
      ε * K.momentConst 0 + 2 * B / δ * (K.momentConst 1 * s ^ (1 / K.order)) := by
  have hint := K.integrable_kernel_mul_of_bound hs x hg hB
  have hQ := K.integrable_kernel hs x
  have hint2 : Integrable (fun y => K.kernel s x y * (g y - g x)) μ := by
    simp only [mul_sub]
    exact hint.sub (hQ.mul_const _)
  have e : K.apply s g x - g x = ∫ y, K.kernel s x y * (g y - g x) ∂μ := by
    have h1 : ∫ y, K.kernel s x y * g x ∂μ = g x := by
      rw [integral_mul_const, hK hs x, one_mul]
    simp only [mul_sub]
    rw [integral_sub hint (hQ.mul_const _), h1]
    rfl
  have hm := K.integrable_moment hs (zero_le_one' ℝ) x
  have hbd : Integrable (fun y => ε * |K.kernel s x y| +
      2 * B / δ * (|K.kernel s x y| * K.scaleDist y x ^ (1 : ℝ))) μ :=
    (hQ.abs.const_mul ε).add (hm.const_mul _)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
  have hpt : ∀ y, ‖K.kernel s x y * (g y - g x)‖ ≤ ε * |K.kernel s x y| +
      2 * B / δ * (|K.kernel s x y| * K.scaleDist y x ^ (1 : ℝ)) := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, Real.rpow_one]
    have hd := K.scaleDist_nonneg y x
    have hQ0 := abs_nonneg (K.kernel s x y)
    by_cases hy : K.scaleDist y x < δ
    · have := hc y hy
      have h2 : 0 ≤ 2 * B / δ * (|K.kernel s x y| * K.scaleDist y x) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this.le hQ0]
    · replace hy := not_lt.1 hy
      have h3 : |g y - g x| ≤ 2 * B := by
        have := abs_sub (g y) (g x)
        linarith [hB y, hB x]
      have h4 : 2 * B ≤ 2 * B / δ * K.scaleDist y x := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
        nlinarith
      have h5 : 0 ≤ ε * |K.kernel s x y| := by positivity
      calc |K.kernel s x y| * |g y - g x| ≤ |K.kernel s x y| * (2 * B / δ * K.scaleDist y x) :=
            mul_le_mul_of_nonneg_left (h3.trans h4) hQ0
        _ = 2 * B / δ * (|K.kernel s x y| * K.scaleDist y x) := by ring
        _ ≤ _ := le_add_of_nonneg_left h5
  have hmo := K.moment_le hs (zero_le_one' ℝ) x
  have h0 := K.integral_abs_kernel_le hs x
  calc |K.apply s g x - g x| = ‖∫ y, K.kernel s x y * (g y - g x) ∂μ‖ := by
        rw [e, Real.norm_eq_abs]
    _ ≤ ∫ y, (ε * |K.kernel s x y| +
          2 * B / δ * (|K.kernel s x y| * K.scaleDist y x ^ (1 : ℝ))) ∂μ :=
        norm_integral_le_of_norm_le hbd (Eventually.of_forall hpt)
    _ = ε * ∫ y, |K.kernel s x y| ∂μ +
          2 * B / δ * ∫ y, |K.kernel s x y| * K.scaleDist y x ^ (1 : ℝ) ∂μ := by
        rw [integral_add (hQ.abs.const_mul ε) (hm.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        have : 0 ≤ 2 * B / δ := by positivity
        gcongr

/-- Approximate identity: `Q_s g (x) → g (x)` as `s ↓ 0` for `g` bounded measurable and
continuous at `x` with respect to `scaleDist`. -/
theorem tendsto_apply_nhdsGT (hK : K.IsConservative) {g : E → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ y, |g y| ≤ B) (x : E)
    (hc : ∀ ε > 0, ∃ δ > 0, ∀ y, K.scaleDist y x < δ → |g y - g x| < ε) :
    Tendsto (fun s => K.apply s g x) (𝓝[>] 0) (𝓝 (g x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hM0 := K.momentConst_nonneg 0
  set ε' : ℝ := ε / (2 * (K.momentConst 0 + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hcδ⟩ := hc ε' hε'pos
  set C : ℝ := 2 * B / δ * K.momentConst 1 with hC
  have hlim : Tendsto (fun s : ℝ => C * s ^ (1 / K.order)) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuous_rpow_const (one_div_pos.2 K.order_pos).le).const_mul C).tendsto 0
    rw [Real.zero_rpow (one_div_pos.2 K.order_pos).ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev := (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hs0
  have h := K.abs_apply_sub_le hK hs0 hg hB x hε'pos hδ hcδ
  rw [Real.dist_eq]
  have h1 : ε' * K.momentConst 0 < ε / 2 := by
    have : ε' * (K.momentConst 0 + 1) = ε / 2 := by
      rw [hε']; field_simp
    nlinarith
  have h2 : 2 * B / δ * (K.momentConst 1 * s ^ (1 / K.order)) = C * s ^ (1 / K.order) := by
    rw [hC]; ring
  rw [h2] at h
  linarith

end RegularityStructures.RegularisingSemigroup

end
