/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Model.Growth
public import RegularityStructures.Analysis.Kernel.Conservative

/-!
# Approximate identity for functions of polynomial growth

For a conservative regularising semigroup `Q`, `Q_s g (x) → g (x)` as `s ↓ 0` when `g` is bounded
and continuous at `x` (`RegularisingSemigroup.tendsto_apply_nhdsGT`). Here the boundedness is
relaxed to polynomial growth, for `parabolicSemigroup`: near `x` the oscillation of `g` is small by
continuity, and far from `x` it is controlled by `d(y, x) + d(y, x)^{n+1}`, whose `|Q_s|`-moments
tend to `0` (this is the input of the injectivity statements in `PolyCompat`, towards
[Hai14, Lemma 5.16]).
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures

namespace RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- Approximate identity under a growth hypothesis on the oscillation: if for every `ε > 0` there
is `A ≥ 0` with `|g y - g x| ≤ ε + A d(y, x) + A d(y, x)^{n+1}`, and `g` is `Q_s`-integrable, then
`Q_s g (x) → g (x)` as `s ↓ 0`. -/
theorem tendsto_apply_nhdsGT_of_growth (hK : K.IsConservative) {g : E → ℝ} (x : E) (n : ℕ)
    (hint : ∀ ⦃s : ℝ⦄, 0 < s → Integrable (fun y => K.kernel s x y * g y) μ)
    (hg : ∀ ε > 0, ∃ A : ℝ, 0 ≤ A ∧ ∀ y, |g y - g x| ≤
      ε + A * K.scaleDist y x + A * K.scaleDist y x ^ (n + 1)) :
    Tendsto (fun s => K.apply s g x) (𝓝[>] 0) (𝓝 (g x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hM0 := K.momentConst_nonneg 0
  set ε' : ℝ := ε / (2 * (K.momentConst 0 + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨A, hA, hpt⟩ := hg ε' hε'pos
  set f : ℝ → ℝ := fun s => A * (K.momentConst 1 * s ^ (1 / K.order)) +
    A * (K.momentConst ((n + 1 : ℕ) : ℝ) * s ^ (((n + 1 : ℕ) : ℝ) / K.order)) with hf
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have h1 : 0 ≤ 1 / K.order := (one_div_pos.2 K.order_pos).le
    have h2 : 0 ≤ ((n + 1 : ℕ) : ℝ) / K.order := div_nonneg (Nat.cast_nonneg _) K.order_pos.le
    have hc : Continuous f :=
      (continuous_const.mul (continuous_const.mul (Real.continuous_rpow_const h1))).add
        (continuous_const.mul (continuous_const.mul (Real.continuous_rpow_const h2)))
    have := hc.tendsto 0
    have e1 : (0 : ℝ) ^ (1 / K.order) = 0 := Real.zero_rpow (one_div_pos.2 K.order_pos).ne'
    have e2 : (0 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / K.order) = 0 :=
      Real.zero_rpow (div_pos (by positivity) K.order_pos).ne'
    simp only [hf, e1, e2, mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hs0
  have hs0 : (0 : ℝ) < s := hs0
  have hgi := hint hs0
  have hQ := K.integrable_kernel hs0 x
  have hm1 := K.integrable_moment hs0 (zero_le_one' ℝ) x
  have hm2 := K.integrable_moment hs0 (Nat.cast_nonneg (n + 1)) x
  simp only [Real.rpow_natCast] at hm2
  simp only [Real.rpow_one] at hm1
  have e : K.apply s g x - g x = ∫ y, K.kernel s x y * (g y - g x) ∂μ := by
    have h1 : ∫ y, K.kernel s x y * g x ∂μ = g x := by
      rw [integral_mul_const, hK hs0 x, one_mul]
    simp only [mul_sub]
    rw [integral_sub hgi (hQ.mul_const _), h1]
    rfl
  have hbd : Integrable (fun y => ε' * |K.kernel s x y| +
      A * (|K.kernel s x y| * K.scaleDist y x) +
      A * (|K.kernel s x y| * K.scaleDist y x ^ (n + 1))) μ :=
    ((hQ.abs.const_mul ε').add (hm1.const_mul A)).add (hm2.const_mul A)
  have hpt' : ∀ y, ‖K.kernel s x y * (g y - g x)‖ ≤ ε' * |K.kernel s x y| +
      A * (|K.kernel s x y| * K.scaleDist y x) +
      A * (|K.kernel s x y| * K.scaleDist y x ^ (n + 1)) := by
    intro y
    rw [Real.norm_eq_abs, abs_mul]
    have := mul_le_mul_of_nonneg_left (hpt y) (abs_nonneg (K.kernel s x y))
    calc |K.kernel s x y| * |g y - g x|
        ≤ |K.kernel s x y| * (ε' + A * K.scaleDist y x + A * K.scaleDist y x ^ (n + 1)) := this
      _ = _ := by ring
  have hmo1 := K.moment_le hs0 (zero_le_one' ℝ) x
  have hmo2 := K.moment_le hs0 (Nat.cast_nonneg (n + 1)) x
  simp only [Real.rpow_natCast] at hmo2
  simp only [Real.rpow_one] at hmo1
  have h0 := K.integral_abs_kernel_le hs0 x
  have hmain : |K.apply s g x - g x| ≤ ε' * K.momentConst 0 + f s := by
    calc |K.apply s g x - g x| = ‖∫ y, K.kernel s x y * (g y - g x) ∂μ‖ := by
          rw [e, Real.norm_eq_abs]
      _ ≤ ∫ y, (ε' * |K.kernel s x y| + A * (|K.kernel s x y| * K.scaleDist y x) +
            A * (|K.kernel s x y| * K.scaleDist y x ^ (n + 1))) ∂μ :=
          norm_integral_le_of_norm_le hbd (Eventually.of_forall hpt')
      _ = ε' * ∫ y, |K.kernel s x y| ∂μ + A * ∫ y, |K.kernel s x y| * K.scaleDist y x ∂μ +
            A * ∫ y, |K.kernel s x y| * K.scaleDist y x ^ (n + 1) ∂μ := by
          have i1 : Integrable (fun y => ε' * |K.kernel s x y|) μ := hQ.abs.const_mul ε'
          have i2 : Integrable (fun y => A * (|K.kernel s x y| * K.scaleDist y x)) μ :=
            hm1.const_mul A
          have i3 : Integrable
              (fun y => A * (|K.kernel s x y| * K.scaleDist y x ^ (n + 1))) μ :=
            hm2.const_mul A
          have i12 : Integrable (fun y => ε' * |K.kernel s x y| +
              A * (|K.kernel s x y| * K.scaleDist y x)) μ := i1.add i2
          rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul,
            integral_const_mul, integral_const_mul]
      _ ≤ _ := by
          simp only [hf]
          have a0 := mul_le_mul_of_nonneg_left h0 hε'pos.le
          have a1 := mul_le_mul_of_nonneg_left hmo1 hA
          have a2 := mul_le_mul_of_nonneg_left hmo2 hA
          linarith
  have h1 : ε' * K.momentConst 0 < ε / 2 := by
    have : ε' * (K.momentConst 0 + 1) = ε / 2 := by
      rw [hε']; field_simp
    nlinarith
  rw [Real.dist_eq]
  linarith

end RegularisingSemigroup

end RegularityStructures

end
