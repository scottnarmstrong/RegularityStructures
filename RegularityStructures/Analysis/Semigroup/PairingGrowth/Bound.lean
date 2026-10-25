/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Increment
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bounds on `∫ Λ_u φ` and its increments (`LocalBall` version)
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}
  {lam : ℝ}

theorem LocalBall.abs_integral_mul_le {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ}
    (hΛ : K.LocalBall Λ x₀ γ A C lam) {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) {φ : E → ℝ} 
    (hφ : K.IsSupported φ x₀ lam) :
    |∫ y, Λ u y * φ y ∂μ| ≤
      (C * ∑ a ∈ A, u ^ (a / K.order) * lam ^ (γ - a)) * ∫ y, |φ y| ∂μ := by
  set B := C * ∑ a ∈ A, u ^ (a / K.order) * lam ^ (γ - a)
  have h := norm_integral_le_of_norm_le (hφ.integrable.abs.const_mul B)
    (f := fun y => Λ u y * φ y) (Filter.Eventually.of_forall fun y => ?_)
  · rw [integral_const_mul] at h
    simpa using h
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hy : K.scaleDist y x₀ ≤ lam
    · exact mul_le_mul_of_nonneg_right (hΛ.abs_le hu hy) (abs_nonneg _)
    · rw [hφ.supp y (not_le.1 hy)]; simp

theorem LocalBall.abs_integral_sub_le [SFinite μ] (hK : K.IsSymmetric)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ}
    (hΛ : K.LocalBall Λ x₀ γ A C lam) (hA : ∀ a ∈ A, -K.order < a) {φ ψ : E → ℝ} {B₁ : ℝ}
    (hlam : 0 < lam) (hB₁ : 0 ≤ B₁) (hφ : K.IsSupported φ x₀ lam) (hψ : K.IsSupported ψ x₀ lam)
    (hgen : K.IsGeneratorPair φ ψ) (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order)) {s s' : ℝ}
    (hs : 0 < s) (hss' : s < s') (hs' : s' ≤ 1) :
    |∫ y, Λ s' y * φ y ∂μ - ∫ y, Λ s y * φ y ∂μ| ≤
      K.incrBound A γ lam (C * (B₁ * lam ^ (-K.order))) s' := by
  set β := C * (B₁ * lam ^ (-K.order)) with hβ
  have hβ0 : 0 ≤ β := mul_nonneg hΛ.nonneg (mul_nonneg hB₁ (Real.rpow_nonneg hlam.le _))
  have hℓ := K.order_pos
  have he : ∀ a ∈ A, -1 < a / K.order := fun a ha => by
    rw [lt_div_iff₀ hℓ]; linarith [hA a ha]
  rw [hΛ.integral_sub_integral_eq_integral hK hJ hφ hψ hgen hs hss' hs', ← Real.norm_eq_abs]
  have hint : IntervalIntegrable (fun u => β * ∑ a ∈ A, u ^ (a / K.order) * lam ^ (γ - a))
      MeasureTheory.volume s s' := by
    refine IntervalIntegrable.const_mul ?_ β
    have := IntervalIntegrable.sum A (f := fun a (u : ℝ) => u ^ (a / K.order) * lam ^ (γ - a))
      (a := s) (b := s') (μ := volume) fun a ha =>
      (intervalIntegral.intervalIntegrable_rpow' (he a ha)).mul_const _
    convert this using 1
    ext u
    simp [Finset.sum_apply]
  calc ‖∫ u in s..s', ∫ y, Λ u y * ψ y ∂μ‖
      ≤ ∫ u in s..s', β * ∑ a ∈ A, u ^ (a / K.order) * lam ^ (γ - a) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hss'.le
          (Filter.Eventually.of_forall fun u hu => ?_) hint
        have hu' : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs.trans hu.1, hu.2.trans hs'⟩
        rw [Real.norm_eq_abs]
        refine (hΛ.abs_integral_mul_le hu' hψ).trans ?_
        have hS : 0 ≤ C * ∑ a ∈ A, u ^ (a / K.order) * lam ^ (γ - a) :=
          mul_nonneg hΛ.nonneg (Finset.sum_nonneg fun a _ =>
            mul_nonneg (Real.rpow_nonneg hu'.1.le _) (Real.rpow_nonneg hlam.le _))
        calc _ ≤ (C * ∑ a ∈ A, u ^ (a / K.order) * lam ^ (γ - a)) * (B₁ * lam ^ (-K.order)) :=
              mul_le_mul_of_nonneg_left hψ1 hS
          _ = _ := by simp only [hβ]; ring
    _ = β * ∑ a ∈ A, ((s' ^ (a / K.order + 1) - s ^ (a / K.order + 1)) / (a / K.order + 1)) *
          lam ^ (γ - a) := by
        have hi : ∀ a ∈ A, IntervalIntegrable (fun u : ℝ => u ^ (a / K.order) * lam ^ (γ - a))
            volume s s' := fun a ha =>
          (intervalIntegral.intervalIntegrable_rpow' (he a ha)).mul_const _
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hi]
        congr 1
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl (he a ha))]
    _ ≤ K.incrBound A γ lam β s' := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha => ?_) hβ0
        have hpos : 0 < a / K.order + 1 := by linarith [he a ha]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
          (sub_le_self _ (Real.rpow_nonneg hs.le _)) hpos.le) (Real.rpow_nonneg hlam.le _)

end RegularityStructures.RegularisingSemigroup

end
