/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGlobal
public import Phi43.Stochastic.StochasticHeatConvergenceCovarianceInterpolation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Time tails of the massive heat kernel

Spatial convolution reduces the bare covariance to a time tail of the massive kernel. The estimates
below give its size and its modulus when the lower endpoint moves. All constants precede the lower
endpoint and spatial variables. In particular, interpolation of the size and endpoint estimates
gives the time power needed for the time-increment bound without a mollifier derivative or a
constant depending on the regularisation scale.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

private theorem massiveHeatKernel_time_power_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → ∀ x : Torus3,
      |massiveHeatKernel (t, x)| ≤ C * t ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := massiveHeatKernel_global_singular_bound
  refine ⟨C, hC, ?_⟩
  intro t ht x
  have hsqrt : 0 < √t := sqrt_pos.mpr ht
  have hsize : √t ≤ torusParabolicSize (t, x) := by
    simp only [torusParabolicSize, abs_of_pos ht]
    exact le_add_of_nonneg_right (torusSpatialNorm_nonneg x)
  have hpow : torusParabolicSize (t, x) ^ (-(3 : ℝ)) ≤ t ^ (-(3 / 2 : ℝ)) := by
    calc
      torusParabolicSize (t, x) ^ (-(3 : ℝ)) ≤ (√t) ^ (-(3 : ℝ)) :=
        rpow_le_rpow_of_nonpos hsqrt hsize (by norm_num)
      _ = t ^ (-(3 / 2 : ℝ)) := by
        rw [sqrt_eq_rpow, ← rpow_mul ht.le]
        norm_num
  rw [abs_of_nonneg (massiveHeatKernel_nonneg _)]
  exact (hbound (t, x) (hsqrt.trans_le hsize)).trans
    (mul_le_mul_of_nonneg_left hpow hC)

theorem integrableOn_massiveHeatKernel_time_tail {a : ℝ} (ha : 0 < a)
    (x : Torus3) :
    IntegrableOn (fun t : ℝ => massiveHeatKernel (t, x)) (Ioi a) := by
  obtain ⟨C, _hC, hbound⟩ := massiveHeatKernel_time_power_bound
  have hmajor := (integrableOn_Ioi_rpow_of_lt
    (by norm_num : -(3 / 2 : ℝ) < -1) ha).const_mul C
  have hmeas : Measurable (fun t : ℝ => massiveHeatKernel (t, x)) :=
    measurable_massiveHeatKernel.comp (measurable_id.prodMk measurable_const)
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs] using hbound (ha.trans ht) x

theorem massiveHeatKernel_time_tail_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ}, 0 < a → ∀ x : Torus3,
      |∫ t : ℝ in Ioi a, massiveHeatKernel (t, x)| ≤
        C * a ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := massiveHeatKernel_time_power_bound
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro a ha x
  have hmajor := (integrableOn_Ioi_rpow_of_lt
    (by norm_num : -(3 / 2 : ℝ) < -1) ha).const_mul C
  have hnorm := norm_integral_le_of_norm_le
    (f := fun t : ℝ => massiveHeatKernel (t, x)) hmajor (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs] using hbound (ha.trans ht) x)
  calc
    |∫ t : ℝ in Ioi a, massiveHeatKernel (t, x)| ≤
        ∫ t : ℝ in Ioi a, C * t ^ (-(3 / 2 : ℝ)) := hnorm
    _ = (2 * C) * a ^ (-(1 / 2 : ℝ)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha]
      norm_num
      ring

theorem massiveHeatKernel_time_tail_increment_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ x : Torus3,
      |(∫ t : ℝ in Ioi a, massiveHeatKernel (t, x)) -
          ∫ t : ℝ in Ioi b, massiveHeatKernel (t, x)| ≤
        C * (b - a) * a ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := massiveHeatKernel_time_power_bound
  refine ⟨C, hC, ?_⟩
  intro a b ha hab x
  rw [intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_massiveHeatKernel_time_tail ha x) hab]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => massiveHeatKernel (t, x)) (a := a) (b := b)
    (C := C * a ^ (-(3 / 2 : ℝ))) (by
      intro t ht
      rw [uIoc_of_le hab] at ht
      have hpow := rpow_le_rpow_of_nonpos ha ht.1.le
        (by norm_num : -(3 / 2 : ℝ) ≤ 0)
      exact (hbound (ha.trans ht.1) x).trans
        (mul_le_mul_of_nonneg_left hpow hC))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab),
    mul_right_comm] using hnorm

theorem massiveHeatKernel_time_tail_fractional_increment_bound
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ x : Torus3,
      |(∫ t : ℝ in Ioi a, massiveHeatKernel (t, x)) -
          ∫ t : ℝ in Ioi b, massiveHeatKernel (t, x)| ≤
        C * (b - a) ^ θ * a ^ (-(1 / 2 + θ : ℝ)) := by
  obtain ⟨A₀, hA₀, hsize⟩ := massiveHeatKernel_time_tail_bound
  obtain ⟨B, hB, hinc⟩ := massiveHeatKernel_time_tail_increment_bound
  let A : ℝ := 2 * A₀
  have hA : 0 ≤ A := mul_nonneg (by norm_num) hA₀
  refine ⟨A ^ (1 - θ) * B ^ θ,
    mul_nonneg (rpow_nonneg hA _) (rpow_nonneg hB _), ?_⟩
  intro a b ha hab x
  have hb : 0 < b := ha.trans_le hab
  have hpow : b ^ (-(1 / 2 : ℝ)) ≤ a ^ (-(1 / 2 : ℝ)) :=
    rpow_le_rpow_of_nonpos ha hab (by norm_num)
  have hsize' :
      |(∫ t : ℝ in Ioi a, massiveHeatKernel (t, x)) -
          ∫ t : ℝ in Ioi b, massiveHeatKernel (t, x)| ≤
        A * a ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ |∫ t : ℝ in Ioi a, massiveHeatKernel (t, x)| +
          |∫ t : ℝ in Ioi b, massiveHeatKernel (t, x)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (∫ t : ℝ in Ioi a, massiveHeatKernel (t, x)) 0
            (∫ t : ℝ in Ioi b, massiveHeatKernel (t, x))
      _ ≤ A₀ * a ^ (-(1 / 2 : ℝ)) + A₀ * b ^ (-(1 / 2 : ℝ)) :=
        add_le_add (hsize ha x) (hsize hb x)
      _ ≤ A₀ * a ^ (-(1 / 2 : ℝ)) + A₀ * a ^ (-(1 / 2 : ℝ)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow hA₀)
      _ = A * a ^ (-(1 / 2 : ℝ)) := by dsimp [A]; ring
  have hsqrt1 : (√a) ^ (-(1 : ℝ)) = a ^ (-(1 / 2 : ℝ)) := by
    rw [sqrt_eq_rpow, ← rpow_mul ha.le]
    norm_num
  have hsqrt3 : (√a) ^ (-(3 : ℝ)) = a ^ (-(3 / 2 : ℝ)) := by
    rw [sqrt_eq_rpow, ← rpow_mul ha.le]
    norm_num
  have hinterp := abs_le_interpolated_of_abs_le_of_abs_le
    hA hB (sub_nonneg.mpr hab) (sqrt_pos.mpr ha) hθ hθ1
    (by simpa only [hsqrt1] using hsize')
    (by simpa only [hsqrt3] using hinc ha hab x)
  have hpower : (√a) ^ (-(1 + 2 * θ : ℝ)) =
      a ^ (-(1 / 2 + θ : ℝ)) := by
    rw [sqrt_eq_rpow, ← rpow_mul ha.le]
    congr 1
    ring
  simpa only [hpower] using hinterp

end RegularityStructures.Phi43

end
