/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceSpatialGradient
public import RegularityStructures.Torus.KernelBoundsGeometry
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Spatial translation modulus of the torus heat kernel

Coordinatewise mean-value estimates on the centred fundamental cube give a global-in-time
spatial modulus at the origin. Integrating its massive version yields the covariance modulus
needed for the space-time increment bound.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

private theorem centered_cube_update {y : Fin 3 → ℝ}
    (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) (i : Fin 3) {r : ℝ}
    (hr : r ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    ∀ j, Function.update y i r j ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using hr
  · simpa only [Function.update_of_ne hji] using hy j

theorem heatKernelLift_coordinate_lipschitz_time_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → ∀ i : Fin 3, ∀ y : Fin 3 → ℝ,
      (∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) →
      ∀ {u v : ℝ}, u ∈ Icc (-1 / 2 : ℝ) (1 / 2) → v ∈ Icc (-1 / 2 : ℝ) (1 / 2) →
      |heatKernelLift t (Function.update y i u) -
        heatKernelLift t (Function.update y i v)| ≤ C * (t ^ (-(2 : ℝ)) + 1) * |u - v| := by
  obtain ⟨C, hC, hbound⟩ := heatKernelLift_first_deriv_uniform_time_bound
  refine ⟨C, hC, ?_⟩
  intro t ht i y hy u v hu hv
  let f : ℝ → ℝ := fun r => heatKernelLift t (Function.update y i r)
  have hderiv (r : ℝ) (hr : r ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
      HasDerivAt f (gaussKernelSpaceLine_first_deriv_tsum t i (Function.update y i r)) r := by
    have hd := hasDerivAt_heatKernelLift_spaceLine ht i (Function.update y i r)
      (centered_cube_update hy i hr)
    simpa only [Function.update_self, Function.update_idem,
      gaussKernelSpaceLine_first_deriv_tsum] using hd
  have hdiff : ∀ r ∈ Icc (-1 / 2 : ℝ) (1 / 2), DifferentiableAt ℝ f r :=
    fun r hr => (hderiv r hr).differentiableAt
  have hgrad : ∀ r ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      ‖deriv f r‖ ≤ C * (t ^ (-(2 : ℝ)) + 1) := by
    intro r hr
    rw [(hderiv r hr).deriv, Real.norm_eq_abs]
    exact hbound ht i (Function.update y i r) (centered_cube_update hy i hr)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hgrad (convex_Icc _ _) hv hu

theorem heatKernelLift_centered_spatial_modulus :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → ∀ y : Fin 3 → ℝ,
      (∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) →
      |heatKernelLift t y - heatKernelLift t 0| ≤
        C * (t ^ (-(2 : ℝ)) + 1) * √(sqNorm3 y) := by
  obtain ⟨C, hC, hcoord⟩ := heatKernelLift_coordinate_lipschitz_time_bound
  refine ⟨3 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro t ht y hy
  let L : ℝ := C * (t ^ (-(2 : ℝ)) + 1)
  have hL : 0 ≤ L := mul_nonneg hC (add_nonneg (rpow_nonneg ht.le _) zero_le_one)
  have hzero : ∀ j : Fin 3, (0 : Fin 3 → ℝ) j ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro j
    norm_num
  have hz : (0 : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by norm_num
  let a : Fin 3 → ℝ := Function.update 0 0 (y 0)
  let b : Fin 3 → ℝ := Function.update a 1 (y 1)
  have ha := centered_cube_update hzero 0 (hy 0)
  have hb := centered_cube_update ha 1 (hy 1)
  have hc : Function.update b 2 (y 2) = y := by
    funext j
    fin_cases j <;> norm_num [b, a, Function.update]
  have h0 : |heatKernelLift t a - heatKernelLift t 0| ≤ L * |y 0| := by
    have hzupdate : Function.update (0 : Fin 3 → ℝ) 0 0 = 0 := by
      simpa only [Pi.zero_apply] using Function.update_eq_self 0 (0 : Fin 3 → ℝ)
    simpa only [a, hzupdate, sub_zero] using
      hcoord ht 0 0 hzero (hy 0) hz
  have h1 : |heatKernelLift t b - heatKernelLift t a| ≤ L * |y 1| := by
    have hbase : Function.update a 1 0 = a := by
      have hval : a 1 = 0 := by norm_num [a, Function.update]
      rw [← hval, Function.update_eq_self]
    simpa only [b, hbase, sub_zero] using hcoord ht 1 a ha (hy 1) hz
  have h2 : |heatKernelLift t y - heatKernelLift t b| ≤ L * |y 2| := by
    have hbase : Function.update b 2 0 = b := by
      have hval : b 2 = 0 := by norm_num [b, a, Function.update]
      rw [← hval, Function.update_eq_self]
    simpa only [hc, hbase, sub_zero] using hcoord ht 2 b hb (hy 2) hz
  have hsum : ∑ j : Fin 3, |y j| ≤ 3 * √(sqNorm3 y) := by
    have hs : 0 ≤ sqNorm3 y := Finset.sum_nonneg fun j _ => sq_nonneg (y j)
    have hcoord_norm (j : Fin 3) : |y j| ≤ √(sqNorm3 y) := by
      apply (Real.le_sqrt (abs_nonneg _) hs).mpr
      rw [sq_abs]
      exact Finset.single_le_sum (fun k _ => sq_nonneg (y k)) (Finset.mem_univ j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hcoord_norm j)
  calc
    _ ≤ |heatKernelLift t y - heatKernelLift t b| +
        (|heatKernelLift t b - heatKernelLift t a| +
          |heatKernelLift t a - heatKernelLift t 0|) :=
      (abs_sub_le _ _ _).trans (add_le_add le_rfl (abs_sub_le _ _ _))
    _ ≤ L * |y 2| + (L * |y 1| + L * |y 0|) := add_le_add h2 (add_le_add h1 h0)
    _ = L * ∑ j : Fin 3, |y j| := by rw [Fin.sum_univ_three]; ring
    _ ≤ L * (3 * √(sqNorm3 y)) := mul_le_mul_of_nonneg_left hsum hL
    _ = (3 * C) * (t ^ (-(2 : ℝ)) + 1) * √(sqNorm3 y) := by dsimp [L]; ring

theorem heatKernel_spatial_modulus_uniform_time :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → ∀ x : Torus3,
      |heatKernel t x - heatKernel t 0| ≤
        C * (t ^ (-(2 : ℝ)) + 1) * torusSpatialNorm x := by
  obtain ⟨C, hC, hbound⟩ := heatKernelLift_centered_spatial_modulus
  refine ⟨C, hC, ?_⟩
  intro t ht x
  have h := hbound ht (torusCenteredRep x) (fun j => by
    simpa only [neg_div] using torusCenteredRep_mem_Icc x j)
  have hzero : heatKernelLift t 0 = heatKernel t 0 := by
    rw [← heatKernel_comp_torusProj_eq_lift]
    congr 1
  simpa only [← heatKernel_eq_centered_lift, hzero, torusSpatialNorm] using h

end RegularityStructures.Phi43

end
