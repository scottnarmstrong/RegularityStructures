/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Moment
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# From local order with growth to `LocalBall`

`LocalBall.of_growth`: if `Λ` is a `Q`-distribution of local order `γ` with growth `q ≥ 0`
(`IsLocalOrderGrowth`), then `LocalBall Λ x₀ γ A (C (1 + lam)^q) lam` for every `lam ≥ 0`.
-/

public section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

/-- The pointwise bound on `|Q_v(y, z)| |Λ_s(z)|` by an explicit sum of kernel moments. -/
theorem abs_kernel_mul_abs_le_of_growth (hd : K.IsMetricScale) {Λ : ℝ → E → ℝ} {x₀ : E}
    {γ q : ℝ} {A : Finset ℝ} {C : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (hA : ∀ a ∈ A, a ≤ γ)
    (hloc : K.IsLocalOrderGrowth Λ x₀ γ A C q) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) {lam : ℝ}
    (hlam : 0 ≤ lam) {y : E} (hy : K.scaleDist y x₀ ≤ lam) (z : E) (k : ℝ) :
    |k| * |Λ s z| ≤ ∑ a ∈ A, (C * s ^ (a / K.order) * 2 ^ (q + (γ - a)) *
      ((1 + lam) ^ (q + (γ - a)) * |k|) +
      C * s ^ (a / K.order) * 2 ^ (q + (γ - a)) * (|k| * K.scaleDist z y ^ (q + (γ - a)))) := by
  have hb : 1 ≤ 1 + lam := by linarith
  have hDw : K.scaleDist z x₀ ≤ K.scaleDist z y + (1 + lam) - 1 := by
    have := hd.triangle z y x₀
    linarith
  calc |k| * |Λ s z|
      ≤ |k| * (C * (1 + K.scaleDist z x₀) ^ q *
          ∑ a ∈ A, s ^ (a / K.order) * K.scaleDist z x₀ ^ (γ - a)) :=
        mul_le_mul_of_nonneg_left (hloc s hs z) (abs_nonneg _)
    _ = ∑ a ∈ A, |k| * (C * s ^ (a / K.order) *
          ((1 + K.scaleDist z x₀) ^ q * K.scaleDist z x₀ ^ (γ - a))) := by
        rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun a ha => by
        have hr : 0 ≤ γ - a := sub_nonneg.2 (hA a ha)
        have h1 := rpow_mul_rpow_le (K.scaleDist_nonneg z x₀) (K.scaleDist_nonneg z y) hb hq hr
          hDw
        have hc : 0 ≤ C * s ^ (a / K.order) := mul_nonneg hC (Real.rpow_nonneg hs.1.le _)
        calc |k| * (C * s ^ (a / K.order) *
              ((1 + K.scaleDist z x₀) ^ q * K.scaleDist z x₀ ^ (γ - a)))
            ≤ |k| * (C * s ^ (a / K.order) * (2 ^ (q + (γ - a)) *
                ((1 + lam) ^ (q + (γ - a)) + K.scaleDist z y ^ (q + (γ - a))))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hc) (abs_nonneg _)
          _ = _ := by ring

theorem LocalBall.kernel_int_of_growth (hd : K.IsMetricScale) {Λ : ℝ → E → ℝ} {x₀ : E}
    {γ q : ℝ} {A : Finset ℝ} {C : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (hA : ∀ a ∈ A, a ≤ γ)
    (hloc : K.IsLocalOrderGrowth Λ x₀ γ A C q) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) {lam : ℝ}
    (hlam : 0 ≤ lam) (h₀ : ℝ) :
    ∃ W : ℝ, ∀ v ∈ Set.Ioc (0 : ℝ) h₀, ∀ y, K.scaleDist y x₀ ≤ lam →
      ∫ z, |K.kernel v y z| * |Λ s z| ∂μ ≤ W := by
  set c : ℝ → ℝ := fun a => C * s ^ (a / K.order) * 2 ^ (q + (γ - a)) with hc
  have hc0 : ∀ a, 0 ≤ c a := fun a =>
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hs.1.le _)) (Real.rpow_nonneg (by norm_num) _)
  refine ⟨∑ a ∈ A, (c a * ((1 + lam) ^ (q + (γ - a)) * K.momentConst 0) +
    c a * (K.momentConst (q + (γ - a)) * h₀ ^ ((q + (γ - a)) / K.order))), ?_⟩
  intro v hv y hy
  have hv0 : 0 < v := hv.1
  have hm : ∀ a ∈ A, 0 ≤ q + (γ - a) := fun a ha => by linarith [sub_nonneg.2 (hA a ha)]
  have hf : Integrable (fun z => |K.kernel v y z|) μ := (K.integrable_kernel hv0 y).abs
  have hg : ∀ a ∈ A, Integrable (fun z => |K.kernel v y z| *
      K.scaleDist z y ^ (q + (γ - a))) μ := fun a ha => K.integrable_moment hv0 (hm a ha) y
  have hint : ∀ a ∈ A, Integrable (fun z => c a * ((1 + lam) ^ (q + (γ - a)) *
      |K.kernel v y z|) + c a * (|K.kernel v y z| * K.scaleDist z y ^ (q + (γ - a)))) μ :=
    fun a ha => ((hf.const_mul _).const_mul _).add ((hg a ha).const_mul _)
  have hD : Integrable (fun z => ∑ a ∈ A, (c a * ((1 + lam) ^ (q + (γ - a)) *
      |K.kernel v y z|) + c a * (|K.kernel v y z| * K.scaleDist z y ^ (q + (γ - a))))) μ :=
    integrable_finsetSum _ hint
  have hle := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _)) hD (Filter.Eventually.of_forall fun z =>
    abs_kernel_mul_abs_le_of_growth hd hC hq hA hloc hs hlam hy z (K.kernel v y z))
  refine hle.trans ?_
  rw [integral_finsetSum _ hint]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [integral_add ((hf.const_mul _).const_mul _) ((hg a ha).const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul]
  have e1 : ∫ z, |K.kernel v y z| * K.scaleDist z y ^ (q + (γ - a)) ∂μ ≤
      K.momentConst (q + (γ - a)) * h₀ ^ ((q + (γ - a)) / K.order) :=
    (K.moment_le hv0 (hm a ha) y).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hv0.le hv.2 (div_nonneg (hm a ha) K.order_pos.le))
      (K.momentConst_nonneg _))
  have e2 : ∫ z, |K.kernel v y z| ∂μ ≤ K.momentConst 0 := K.integral_abs_kernel_le hv0 y
  have hb0 : 0 ≤ (1 + lam) ^ (q + (γ - a)) := Real.rpow_nonneg (by linarith) _
  have h5 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 hb0) (hc0 a)
  have h6 := mul_le_mul_of_nonneg_left e1 (hc0 a)
  linarith [h5, h6]

theorem LocalBall.of_growth (hd : K.IsMetricScale) {Λ : ℝ → E → ℝ} {x₀ : E} {γ q : ℝ}
    {A : Finset ℝ} {C : ℝ} (hΛ : Λ ∈ K.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hA : ∀ a ∈ A, a ≤ γ)
    (hloc : K.IsLocalOrderGrowth Λ x₀ γ A C q) {lam : ℝ} (hlam : 0 ≤ lam) :
    K.LocalBall Λ x₀ γ A (C * (1 + lam) ^ q) lam where
  mem := hΛ
  meas := hΛm
  nonneg := mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
  le := hA
  kernel_int := fun _ hs h₀ =>
    LocalBall.kernel_int_of_growth hd hC hq hA hloc hs hlam h₀
  ball u hu y hy := by
    refine (hloc u hu y).trans ?_
    have h1 : (1 + K.scaleDist y x₀) ^ q ≤ (1 + lam) ^ q :=
      Real.rpow_le_rpow (by linarith [K.scaleDist_nonneg y x₀]) (by linarith) hq
    have hS : ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a) ≤
        ∑ a ∈ A, u ^ (a / K.order) * lam ^ (γ - a) :=
      Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (K.scaleDist_nonneg _ _) hy (sub_nonneg.2 (hA a ha)))
        (Real.rpow_nonneg hu.1.le _)
    have hS0 : 0 ≤ ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a) :=
      Finset.sum_nonneg fun a _ => mul_nonneg (Real.rpow_nonneg hu.1.le _)
        (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _)
    calc C * (1 + K.scaleDist y x₀) ^ q * ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a)
        ≤ C * (1 + lam) ^ q * ∑ a ∈ A, u ^ (a / K.order) * lam ^ (γ - a) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) hS hS0
            (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))

end RegularityStructures.RegularisingSemigroup

end
