/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Covariance Fubini for measurable versions

These generic analytic lemmas convert a uniform second-moment bound to joint product
integrability, and transfer the second moment of an integral through a covariance identity.
They do not assume joint measurability of any raw white-noise evaluation family.
The heat-pairing application must prove all their inputs.
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

private theorem abs_product_le_half_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith only [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

theorem integrable_weighted_covariance_product_of_second_moment_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α → β → ℝ} {φ : α → ℝ} {C : ℝ}
    (hfm : Measurable (fun q : α × β => f q.1 q.2))
    (hf : ∀ x, MemLp (f x) 2 ν) (hC : ∀ x, (∫ b, f x b ^ 2 ∂ν) ≤ C)
    (hφm : Measurable φ) (hφ : Integrable φ μ) :
    Integrable (fun q : (α × α) × β =>
      (φ q.1.1 * φ q.1.2) * (f q.1.1 q.2 * f q.1.2 q.2))
      ((μ.prod μ).prod ν) := by
  let H : (α × α) × β → ℝ := fun q =>
    (φ q.1.1 * φ q.1.2) * (f q.1.1 q.2 * f q.1.2 q.2)
  have hHm : Measurable H :=
    ((hφm.comp (measurable_fst.comp measurable_fst)).mul
      (hφm.comp (measurable_snd.comp measurable_fst))).mul
      ((hfm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
        (hfm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hprod (x y : α) : Integrable (fun b => f x b * f y b) ν :=
    (hf x).integrable_mul (hf y)
  have habs (x y : α) : (∫ b, |f x b * f y b| ∂ν) ≤ C := by
    calc
      _ ≤ ∫ b, (f x b ^ 2 + f y b ^ 2) / 2 ∂ν :=
        integral_mono (hprod x y).norm (((hf x).integrable_sq.add (hf y).integrable_sq).div_const 2)
          (fun b => abs_product_le_half_sq _ _)
      _ = ((∫ b, f x b ^ 2 ∂ν) + ∫ b, f y b ^ 2 ∂ν) / 2 := by
        simp_rw [div_eq_mul_inv]
        rw [integral_mul_const, integral_add (hf x).integrable_sq (hf y).integrable_sq]
      _ ≤ C := by linarith only [hC x, hC y]
  apply (integrable_prod_iff hHm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with q
    exact (hprod q.1 q.2).const_mul (φ q.1 * φ q.2)
  · apply ((hφ.norm.mul_prod hφ.norm).mul_const C).mono'
      hHm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [] with q
    rw [Real.norm_of_nonneg (integral_nonneg fun b => norm_nonneg _)]
    calc
      _ = (‖φ q.1‖ * ‖φ q.2‖) * ∫ b, |f q.1 b * f q.2 b| ∂ν := by
        simp only [H, norm_mul, Real.norm_eq_abs, abs_mul]
        exact integral_const_mul _ _
      _ ≤ (‖φ q.1‖ * ‖φ q.2‖) * C :=
        mul_le_mul_of_nonneg_left (habs q.1 q.2) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem integral_average_sq_eq_of_covariance
    {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Ω]
    {μ : Measure α} {ν : Measure β} {P : Measure Ω}
    [SFinite μ] [SFinite ν] [SFinite P]
    {X : α → Ω → ℝ} {k : α → β → ℝ}
    (hX : Integrable (fun q : (α × α) × Ω => X q.1.1 q.2 * X q.1.2 q.2)
      ((μ.prod μ).prod P))
    (hk : Integrable (fun q : (α × α) × β => k q.1.1 q.2 * k q.1.2 q.2)
      ((μ.prod μ).prod ν))
    (hcov : ∀ x y, (∫ ω, X x ω * X y ω ∂P) = ∫ b, k x b * k y b ∂ν) :
    (∫ ω, (∫ x, X x ω ∂μ) ^ 2 ∂P) = ∫ b, (∫ x, k x b ∂μ) ^ 2 ∂ν := by
  calc
    _ = ∫ ω, (∫ q : α × α, X q.1 ω * X q.2 ω ∂(μ.prod μ)) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [pow_two]
      exact (integral_prod_mul (μ := μ) (ν := μ) (fun x => X x ω) (fun x => X x ω)).symm
    _ = ∫ q : α × α, (∫ ω, X q.1 ω * X q.2 ω ∂P) ∂(μ.prod μ) :=
      integral_integral_swap hX.swap
    _ = ∫ q : α × α, (∫ b, k q.1 b * k q.2 b ∂ν) ∂(μ.prod μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => hcov q.1 q.2
    _ = ∫ b, (∫ q : α × α, k q.1 b * k q.2 b ∂(μ.prod μ)) ∂ν :=
      integral_integral_swap hk
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with b
      rw [pow_two]
      exact integral_prod_mul (μ := μ) (ν := μ) (fun x => k x b) (fun x => k x b)

end RegularityStructures.Phi43

end
