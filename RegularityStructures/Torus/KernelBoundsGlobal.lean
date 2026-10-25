/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGeometry
public import RegularityStructures.Torus.KernelBoundsLargeTime

/-!
# A global parabolic majorant for the massive heat kernel

The local singular estimate and the exponential large-time estimate combine into one estimate on
all nonzero space-time points.
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures

theorem massiveHeatKernel_global_singular_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SpaceTime, 0 < torusParabolicSize z →
      massiveHeatKernel z ≤ C * torusParabolicSize z ^ (-(3 : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := massiveHeatKernel_singular_bound
  obtain ⟨C₁, hC₁⟩ := massiveHeatKernel_exponential_bound
  obtain ⟨C₂, hC₂⟩ := heatKernel_le_time_singular
  let A : ℝ := max C₂ 0
  let E : ℝ := max C₁ 0
  let C : ℝ := max C₀ 0 + 4096 * A + 512 * E
  have hA : 0 ≤ A := le_max_right C₂ 0
  have hE : 0 ≤ E := le_max_right C₁ 0
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro z hz
  by_cases ht : z.1 ≤ 0
  · rw [massiveHeatKernel, ite_eq_right (not_lt.mpr ht)]
    exact mul_nonneg hC (Real.rpow_nonneg (torusParabolicSize_nonneg z) _)
  have htpos : 0 < z.1 := lt_of_not_ge ht
  by_cases hs : torusParabolicSize z ≤ 1
  · have hconst : C₀ ≤ C := by
      dsimp [C]
      linarith [le_max_left C₀ 0, hA, hE]
    exact (hC₀ z hz hs).2.trans (mul_le_mul_of_nonneg_right hconst
      (Real.rpow_nonneg (torusParabolicSize_nonneg z) _))
  have hd : torusSpatialNorm z.2 ≤ (7 : ℝ) / 8 :=
    torusSpatialNorm_le_seven_eighth z.2
  by_cases ht1 : 1 ≤ z.1
  · have hsqrt : 1 ≤ √z.1 := by
      apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt htpos.le]
      linarith
    have hsize : torusParabolicSize z ≤ 1 + 2 * √z.1 := by
      unfold torusParabolicSize
      rw [abs_of_pos htpos]
      linarith [hd, Real.sqrt_nonneg z.1]
    have hu : 0 ≤ 2 * √z.1 := by positivity
    have hpoly := exp_neg_sq_div_four_mul_one_add_cube_le hu
    have hprod : exp (-z.1) * torusParabolicSize z ^ (3 : ℕ) ≤ 512 := by
      have hpow : torusParabolicSize z ^ (3 : ℕ) ≤
          (1 + 2 * √z.1) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (torusParabolicSize_nonneg z) hsize 3
      have hexpform : exp (-((2 * √z.1) ^ 2) / 4) = exp (-z.1) := by
        congr 1
        rw [show (2 * √z.1) ^ 2 = 4 * z.1 by
          rw [mul_pow, Real.sq_sqrt htpos.le]
          ring]
        ring
      rw [← hexpform]
      exact (mul_le_mul_of_nonneg_left hpow (exp_nonneg _)).trans hpoly
    have hdiv : exp (-z.1) ≤ 512 * torusParabolicSize z ^ (-(3 : ℝ)) := by
      have hpos : 0 < torusParabolicSize z ^ (3 : ℕ) := by positivity
      have h := (le_div_iff₀ hpos).2 hprod
      calc
        exp (-z.1) ≤ 512 / torusParabolicSize z ^ (3 : ℕ) := h
        _ = 512 * torusParabolicSize z ^ (-(3 : ℝ)) := by
          simp [div_eq_mul_inv]
    have hG := hC₁ z ht1
    have hEconst : C₁ ≤ E := le_max_left C₁ 0
    have hG' : massiveHeatKernel z ≤ 512 * E *
        torusParabolicSize z ^ (-(3 : ℝ)) := by
      calc
        massiveHeatKernel z ≤ C₁ * exp (-z.1) := hG
        _ ≤ E * exp (-z.1) := mul_le_mul_of_nonneg_right hEconst (exp_nonneg _)
        _ ≤ 512 * E * torusParabolicSize z ^ (-(3 : ℝ)) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            mul_le_mul_of_nonneg_left hdiv hE
    have hmax : 0 ≤ max C₀ 0 := le_max_right C₀ 0
    exact hG'.trans (by
      apply mul_le_mul_of_nonneg_right _
        (Real.rpow_nonneg (torusParabolicSize_nonneg z) _)
      dsimp [C]
      linarith [hA, hE, hmax, le_max_left C₀ 0])
  · have ht1' : z.1 ≤ 1 := le_of_not_ge ht1
    have hsqrt_lower : (1 : ℝ) / 8 < √z.1 := by
      unfold torusParabolicSize at hs
      rw [abs_of_pos htpos] at hs
      linarith [hd, Real.sqrt_nonneg z.1]
    have hsquare : (√z.1) ^ 2 = z.1 := Real.sq_sqrt htpos.le
    have ht_lower : (1 : ℝ) / 64 < z.1 := by
      nlinarith [hsquare]
    have hpow : z.1 ^ (-(3 : ℝ) / 2) ≤ (1 / 64 : ℝ) ^ (-(3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (le_of_lt ht_lower) (by norm_num)
    have hpow' : z.1 ^ (-(3 : ℝ) / 2) ≤ 512 := by
      calc
        z.1 ^ (-(3 : ℝ) / 2) ≤ (1 / 64 : ℝ) ^ (-(3 : ℝ) / 2) := hpow
        _ ≤ 512 := by norm_num [Real.rpow_neg]
    have hheat := hC₂ z.1 ⟨htpos, ht1'⟩ z.2
    have hheat' : heatKernel z.1 z.2 ≤ A * 512 := by
      calc
        heatKernel z.1 z.2 ≤ C₂ * z.1 ^ (-(3 : ℝ) / 2) := hheat
        _ ≤ A * z.1 ^ (-(3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (le_max_left C₂ 0) (Real.rpow_nonneg htpos.le _)
        _ ≤ A * 512 := mul_le_mul_of_nonneg_left hpow' hA
    have hG : massiveHeatKernel z ≤ A * 512 := by
      simp only [massiveHeatKernel, htpos, ite_true]
      have hexp : exp (-z.1) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      simpa [mul_comm] using
        (mul_le_of_le_one_right (heatKernel_nonneg htpos z.2) hexp).trans hheat'
    have hsize : torusParabolicSize z ≤ 2 := by
      unfold torusParabolicSize
      rw [abs_of_pos htpos]
      have hsqrtupper : √z.1 ≤ 1 := by
        apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
        rw [Real.sq_sqrt htpos.le]
        linarith
      linarith [hd, hsqrtupper]
    have hspow : (1 / 8 : ℝ) ≤ torusParabolicSize z ^ (-(3 : ℝ)) := by
      have h : (2 : ℝ) ^ (-(3 : ℝ)) ≤
          torusParabolicSize z ^ (-(3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hz hsize (by norm_num)
      convert h using 1; norm_num
    have hG' : massiveHeatKernel z ≤ 4096 * A *
        torusParabolicSize z ^ (-(3 : ℝ)) := by
      nlinarith [hG, hspow, hA]
    exact hG'.trans (by
      apply mul_le_mul_of_nonneg_right _
        (Real.rpow_nonneg (torusParabolicSize_nonneg z) _)
      dsimp [C]
      linarith [hA, hE, le_max_right C₀ 0, le_max_left C₀ 0])

end RegularityStructures

end
