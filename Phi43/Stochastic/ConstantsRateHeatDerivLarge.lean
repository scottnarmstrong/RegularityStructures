/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateHeatDeriv

/-!
# Derivatives of the lifted heat kernel at large times

For `τ ≥ 1/2` each Gaussian term of the lattice sums for the first spatial and the time derivative
of `heatKernelLift τ` is dominated by a constant multiple of the term at time `2τ`, whose sum is the
heat kernel at time `2τ ≥ 1`, bounded by `heatKernel_le_large_time`.
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures

theorem abs_mul_exp_neg_sq_le_one (a : ℝ) : |a| * exp (-(a ^ 2)) ≤ 1 := by
  have h1 : |a| ≤ exp (a ^ 2) := by
    have := Real.add_one_le_exp (a ^ 2)
    nlinarith [sq_abs a, abs_nonneg a, sq_nonneg (|a| - 1)]
  calc
    |a| * exp (-(a ^ 2)) ≤ exp (a ^ 2) * exp (-(a ^ 2)) :=
      mul_le_mul_of_nonneg_right h1 (exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

theorem mul_exp_neg_le_one {b : ℝ} : b * exp (-b) ≤ 1 := by
  have h1 : b ≤ exp b := by linarith [Real.add_one_le_exp b]
  calc
    b * exp (-b) ≤ exp b * exp (-b) := mul_le_mul_of_nonneg_right h1 (exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

theorem gaussKernel_eq_two_mul {τ : ℝ} (hτ : 0 < τ) (v : Fin 3 → ℝ) :
    gaussKernel τ v = (2 : ℝ) ^ ((3 : ℝ) / 2) * gaussKernel (2 * τ) v *
      exp (-sqNorm3 v / (8 * τ)) := by
  unfold gaussKernel
  have h1 : (4 * π * τ) ^ (-(3 : ℝ) / 2) =
      (2 : ℝ) ^ ((3 : ℝ) / 2) * (4 * π * (2 * τ)) ^ (-(3 : ℝ) / 2) := by
    have hpos : 0 ≤ 4 * π * τ := by positivity
    have : 4 * π * (2 * τ) = 2 * (4 * π * τ) := by ring
    rw [this, Real.mul_rpow (x := 2) (y := 4 * π * τ) (by norm_num) hpos]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((3 : ℝ) / 2) := by positivity
    have : (2 : ℝ) ^ (-(3 : ℝ) / 2) = ((2 : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
      rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg (by norm_num)]
    rw [this]
    field_simp
  have h2 : exp (-sqNorm3 v / (4 * τ)) = exp (-sqNorm3 v / (4 * (2 * τ))) * exp (-sqNorm3 v / (8 * τ)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [h1, h2]
  ring

theorem two_rpow_three_halves : (2 : ℝ) ^ ((3 : ℝ) / 2) = 2 * √2 := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

theorem abs_mul_exp_neg_sq_div_le {τ : ℝ} (hτ : 0 < τ) (u : ℝ) :
    |u| * exp (-(u ^ 2) / (8 * τ)) ≤ √(8 * τ) := by
  have hs : 0 < √(8 * τ) := Real.sqrt_pos.mpr (by positivity)
  have hsq : √(8 * τ) ^ 2 = 8 * τ := Real.sq_sqrt (by positivity)
  have h := abs_mul_exp_neg_sq_le_one (u / √(8 * τ))
  have h1 : -((u / √(8 * τ)) ^ 2) = -(u ^ 2) / (8 * τ) := by
    rw [div_pow, hsq]
    ring
  rw [h1, abs_div, abs_of_pos hs] at h
  have h2 : |u| * exp (-(u ^ 2) / (8 * τ)) = √(8 * τ) * (|u| / √(8 * τ) * exp (-(u ^ 2) / (8 * τ))) := by
    field_simp
  rw [h2]
  calc
    √(8 * τ) * (|u| / √(8 * τ) * exp (-(u ^ 2) / (8 * τ))) ≤ √(8 * τ) * 1 :=
      mul_le_mul_of_nonneg_left h hs.le
    _ = √(8 * τ) := mul_one _

theorem gauss_space_deriv_dom {τ : ℝ} (hτ : 0 < τ) (v : Fin 3 → ℝ) (i : Fin 3) :
    |gaussKernel τ v * (-(v i / (2 * τ)))| ≤ 4 / √τ * gaussKernel (2 * τ) v := by
  have hg2 : 0 ≤ gaussKernel (2 * τ) v := gaussKernel_nonneg (by positivity) v
  rw [gaussKernel_eq_two_mul hτ v, abs_mul, abs_neg, abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℝ) / 2)), abs_of_nonneg hg2,
    abs_of_nonneg (exp_nonneg _), abs_of_pos (by positivity : (0 : ℝ) < 2 * τ)]
  have hS : v i ^ 2 ≤ sqNorm3 v := by
    unfold sqNorm3
    exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hE : exp (-sqNorm3 v / (8 * τ)) ≤ exp (-(v i ^ 2) / (8 * τ)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hu := abs_mul_exp_neg_sq_div_le hτ (v i)
  have hroot : 0 < √τ := Real.sqrt_pos.mpr hτ
  have hroot2 : √τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have h8 : √(8 * τ) = 2 * √2 * √τ := by
    rw [show 8 * τ = (2 * √2) ^ 2 * τ by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [two_rpow_three_halves]
  have hc : (2 * √2) * (2 * √2 * √τ) / (2 * τ) = 4 / √τ := by
    have : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith [this, hroot2]
  calc
    2 * √2 * gaussKernel (2 * τ) v * exp (-sqNorm3 v / (8 * τ)) * (|v i| / (2 * τ)) =
        (2 * √2) * gaussKernel (2 * τ) v * (|v i| * exp (-sqNorm3 v / (8 * τ)) / (2 * τ)) := by
      ring
    _ ≤ (2 * √2) * gaussKernel (2 * τ) v * (√(8 * τ) / (2 * τ)) := by
      gcongr
      calc
        |v i| * exp (-sqNorm3 v / (8 * τ)) ≤ |v i| * exp (-(v i ^ 2) / (8 * τ)) :=
          mul_le_mul_of_nonneg_left hE (abs_nonneg _)
        _ ≤ √(8 * τ) := hu
    _ = 4 / √τ * gaussKernel (2 * τ) v := by
      rw [h8, ← hc]
      ring

theorem iteratedDeriv_one_gaussKernelSpaceLine_lattice {t : ℝ} (i : Fin 3) (y : Fin 3 → ℝ)
    (k : Fin 3 → ℤ) :
    iteratedDeriv 1 (gaussKernelSpaceLine t i y k) (y i) =
      gaussKernel t (y + fun j => (k j : ℝ)) * (-((y i + (k i : ℝ)) / (2 * t))) := by
  have h₁ : ∀ (c r : ℝ), iteratedDeriv 1 (expPowFun c 2) r = -(c * 2 * r) * expPowFun c 2 r := by
    intro c r
    rw [iteratedDeriv_one]
    simpa using (hasDerivAt_expPowFun c 2 r).deriv
  fin_cases i
  · rw [iteratedDeriv_gaussKernelSpaceLine, h₁]
    simp [gaussKernelSpaceLineCoeff, gaussKernel_eq_prod, expPowFun, Fin.prod_univ_three]
    ring
  · rw [iteratedDeriv_gaussKernelSpaceLine, h₁]
    simp [gaussKernelSpaceLineCoeff, gaussKernel_eq_prod, expPowFun, Fin.prod_univ_three]
    ring
  · rw [iteratedDeriv_gaussKernelSpaceLine, h₁]
    simp [gaussKernelSpaceLineCoeff, gaussKernel_eq_prod, expPowFun, Fin.prod_univ_three]
    ring

theorem gauss_time_deriv_dom {τ : ℝ} (hτ : 0 < τ) (v : Fin 3 → ℝ) :
    |gaussKernel τ v * ∑ i : Fin 3, (4 * ((4 * τ)⁻¹) ^ 2 * (v i) ^ 2 - 2 * ((4 * τ)⁻¹))| ≤
      10 / τ * gaussKernel (2 * τ) v := by
  have hg2 : 0 ≤ gaussKernel (2 * τ) v := gaussKernel_nonneg (by positivity) v
  have hsum : ∑ i : Fin 3, (4 * ((4 * τ)⁻¹) ^ 2 * (v i) ^ 2 - 2 * ((4 * τ)⁻¹)) =
      sqNorm3 v / (4 * τ ^ 2) - 3 / (2 * τ) := by
    unfold sqNorm3
    simp only [Fin.sum_univ_three]
    field_simp
    ring
  have hS0 : 0 ≤ sqNorm3 v := Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [hsum, gaussKernel_eq_two_mul hτ v, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ (2 : ℝ) ^ ((3 : ℝ) / 2) * gaussKernel (2 * τ) v * exp (-sqNorm3 v / (8 * τ)))]
  have hE1 : exp (-sqNorm3 v / (8 * τ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hbe : sqNorm3 v * exp (-sqNorm3 v / (8 * τ)) ≤ 8 * τ := by
    have h := mul_exp_neg_le_one (b := sqNorm3 v / (8 * τ))
    have hexp : exp (-(sqNorm3 v / (8 * τ))) = exp (-sqNorm3 v / (8 * τ)) := by
      congr 1
      ring
    rw [hexp] at h
    have : sqNorm3 v * exp (-sqNorm3 v / (8 * τ)) =
        8 * τ * (sqNorm3 v / (8 * τ) * exp (-sqNorm3 v / (8 * τ))) := by
      field_simp
    rw [this]
    nlinarith
  have habs : |sqNorm3 v / (4 * τ ^ 2) - 3 / (2 * τ)| ≤ sqNorm3 v / (4 * τ ^ 2) + 3 / (2 * τ) := by
    rw [abs_le]
    constructor
    · have : 0 ≤ sqNorm3 v / (4 * τ ^ 2) := by positivity
      have : 0 ≤ 3 / (2 * τ) := by positivity
      linarith
    · have : 0 ≤ 3 / (2 * τ) := by positivity
      linarith
  have hsq2 : √2 ≤ 10 / 7 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  rw [two_rpow_three_halves]
  have hE : exp (-sqNorm3 v / (8 * τ)) * (sqNorm3 v / (4 * τ ^ 2) + 3 / (2 * τ)) ≤
      7 / (2 * τ) := by
    have h1 : exp (-sqNorm3 v / (8 * τ)) * (sqNorm3 v / (4 * τ ^ 2)) ≤ 2 / τ := by
      have : exp (-sqNorm3 v / (8 * τ)) * (sqNorm3 v / (4 * τ ^ 2)) =
          (sqNorm3 v * exp (-sqNorm3 v / (8 * τ))) / (4 * τ ^ 2) := by ring
      rw [this, div_le_iff₀ (by positivity)]
      calc
        sqNorm3 v * exp (-sqNorm3 v / (8 * τ)) ≤ 8 * τ := hbe
        _ = 2 / τ * (4 * τ ^ 2) := by field_simp; ring
    have h2 : exp (-sqNorm3 v / (8 * τ)) * (3 / (2 * τ)) ≤ 3 / (2 * τ) := by
      calc
        exp (-sqNorm3 v / (8 * τ)) * (3 / (2 * τ)) ≤ 1 * (3 / (2 * τ)) :=
          mul_le_mul_of_nonneg_right hE1 (by positivity)
        _ = 3 / (2 * τ) := one_mul _
    have : 7 / (2 * τ) = 2 / τ + 3 / (2 * τ) := by field_simp; ring
    rw [this, mul_add]
    linarith
  calc
    2 * √2 * gaussKernel (2 * τ) v * exp (-sqNorm3 v / (8 * τ)) *
        |sqNorm3 v / (4 * τ ^ 2) - 3 / (2 * τ)| ≤
        2 * √2 * gaussKernel (2 * τ) v * exp (-sqNorm3 v / (8 * τ)) *
          (sqNorm3 v / (4 * τ ^ 2) + 3 / (2 * τ)) := by
      gcongr
    _ = (2 * √2) * gaussKernel (2 * τ) v *
        (exp (-sqNorm3 v / (8 * τ)) * (sqNorm3 v / (4 * τ ^ 2) + 3 / (2 * τ))) := by ring
    _ ≤ (2 * √2) * gaussKernel (2 * τ) v * (7 / (2 * τ)) := by gcongr
    _ ≤ (2 * (10 / 7)) * gaussKernel (2 * τ) v * (7 / (2 * τ)) := by
      gcongr
    _ = 10 / τ * gaussKernel (2 * τ) v := by
      field_simp

theorem summable_gaussKernel_centered {t : ℝ} (ht : 0 < t) {c : Fin 3 → ℝ}
    (hc : ∀ j, c j ∈ Icc (-1 : ℝ) 2) :
    Summable (fun k : Fin 3 → ℤ => gaussKernel t (c + fun j => (k j : ℝ))) :=
  Summable.of_norm_bounded (summable_gaussian_vector_majorant ht)
    (fun k => gaussKernel_le_uniform_majorant ht hc k)

theorem heatLift_space_hasDerivAt_large :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 1 / 2 ≤ τ → ∀ (y : Fin 3 → ℝ) (i : Fin 3),
      ∃ d : ℝ, HasDerivAt (fun s => heatKernelLift τ (Function.update y i s)) d (y i) ∧
        |d| ≤ C := by
  obtain ⟨M, hM⟩ := heatKernel_le_large_time
  refine ⟨8 * max M 0, by positivity, ?_⟩
  intro τ hτ y i
  have hτ0 : 0 < τ := by linarith
  obtain ⟨n, hn⟩ := exists_int_lift_centered y
  set c : Fin 3 → ℝ := torusCenteredRep (torusProj y) with hc
  have hcI : ∀ j, c j ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro j
    have := torusCenteredRep_mem_Icc (torusProj y) j
    simpa [neg_div] using this
  have hc12 : ∀ j, c j ∈ Icc (-1 : ℝ) 2 := fun j =>
    ⟨by linarith [(hcI j).1], by linarith [(hcI j).2]⟩
  have hder := hasDerivAt_heatKernelLift_spaceLine hτ0 i c hcI
  have hyi : y i - (n i : ℝ) = c i := by
    have := congrFun hn i
    simp only [Pi.add_apply] at this
    linarith
  refine ⟨gaussKernelSpaceLine_first_deriv_tsum τ i c, ?_, ?_⟩
  · have hfun : (fun s => heatKernelLift τ (Function.update y i s)) =
        fun s => heatKernelLift τ (Function.update c i (s - n i)) := by
      funext s
      exact heatKernelLift_update_eq τ y i n hn s
    rw [hfun]
    have hd2 : HasDerivAt (fun s => heatKernelLift τ (Function.update c i s))
        (gaussKernelSpaceLine_first_deriv_tsum τ i c) (y i - n i) := by
      rw [hyi]
      exact hder
    exact hd2.comp_sub_const (y i) (n i)
  · have hroot : (1 / 2 : ℝ) ≤ √τ := by
      rw [show (1 / 2 : ℝ) = √(1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hrootpos : 0 < √τ := by linarith
    have hterm : ∀ k : Fin 3 → ℤ, iteratedDeriv 1 (gaussKernelSpaceLine τ i c k) (c i) =
        gaussKernel τ (c + fun j => (k j : ℝ)) * (-((c i + (k i : ℝ)) / (2 * τ))) :=
      fun k => iteratedDeriv_one_gaussKernelSpaceLine_lattice i c k
    have hsum2 : Summable (fun k : Fin 3 → ℤ =>
        4 / √τ * gaussKernel (2 * τ) (c + fun j => (k j : ℝ))) :=
      (summable_gaussKernel_centered (by positivity) hc12).mul_left _
    have hdom : ∀ k : Fin 3 → ℤ, ‖iteratedDeriv 1 (gaussKernelSpaceLine τ i c k) (c i)‖ ≤
        4 / √τ * gaussKernel (2 * τ) (c + fun j => (k j : ℝ)) := by
      intro k
      rw [hterm k, Real.norm_eq_abs]
      have := gauss_space_deriv_dom hτ0 (c + fun j => (k j : ℝ)) i
      simpa [Pi.add_apply] using this
    have hsumN : Summable (fun k : Fin 3 → ℤ =>
        ‖iteratedDeriv 1 (gaussKernelSpaceLine τ i c k) (c i)‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hdom hsum2
    have hbound := tsum_of_norm_bounded hsum2.hasSum hdom
    unfold gaussKernelSpaceLine_first_deriv_tsum
    rw [← Real.norm_eq_abs]
    refine hbound.trans ?_
    rw [tsum_mul_left]
    have hH : ∑' k : Fin 3 → ℤ, gaussKernel (2 * τ) (c + fun j => (k j : ℝ)) =
        heatKernel (2 * τ) (torusProj c) := by
      rw [heatKernel_comp_torusProj_eq_lift]
      rfl
    rw [hH]
    have hMb : heatKernel (2 * τ) (torusProj c) ≤ max M 0 :=
      (hM (2 * τ) (by linarith) _).trans (le_max_left _ _)
    have h4 : 4 / √τ ≤ 8 := by
      rw [div_le_iff₀ hrootpos]
      linarith
    calc
      4 / √τ * heatKernel (2 * τ) (torusProj c) ≤ 8 * max M 0 := by
        apply mul_le_mul h4 hMb (heatKernel_nonneg (by linarith) _) (by norm_num)
      _ = 8 * max M 0 := rfl

theorem heatLift_time_hasDerivAt_large :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 1 / 2 ≤ τ → ∀ y : Fin 3 → ℝ,
      ∃ d : ℝ, HasDerivAt (fun σ => heatKernelLift σ y) d τ ∧ |d| ≤ C := by
  obtain ⟨M, hM⟩ := heatKernel_le_large_time
  refine ⟨20 * max M 0, by positivity, ?_⟩
  intro τ hτ y
  have hτ0 : 0 < τ := by linarith
  set c : Fin 3 → ℝ := torusCenteredRep (torusProj y) with hc
  have hcI : ∀ j, c j ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro j
    have := torusCenteredRep_mem_Icc (torusProj y) j
    simpa [neg_div] using this
  have hc12 : ∀ j, c j ∈ Icc (-1 : ℝ) 2 := fun j =>
    ⟨by linarith [(hcI j).1], by linarith [(hcI j).2]⟩
  have hder := hasDerivAt_heatKernelLift_time hτ0 c hcI
  refine ⟨gaussKernelTimeDerivativeTsum τ c, ?_, ?_⟩
  · have hfun : (fun σ => heatKernelLift σ y) = fun σ => heatKernelLift σ c := by
      funext σ
      exact heatKernelLift_eq_centered σ y
    rw [hfun]
    exact hder
  · have hterm : ∀ k : Fin 3 → ℤ, ∑ i : Fin 3, iteratedDeriv 2 (gaussKernelSpaceLine τ i c k) (c i) =
        gaussKernel τ (c + fun j => (k j : ℝ)) *
          ∑ i : Fin 3, (4 * ((4 * τ)⁻¹) ^ 2 * (c i + (k i : ℝ)) ^ 2 - 2 * ((4 * τ)⁻¹)) := by
      intro k
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact gaussKernel_space_second_eq_lattice i c k
    have hsum2 : Summable (fun k : Fin 3 → ℤ =>
        10 / τ * gaussKernel (2 * τ) (c + fun j => (k j : ℝ))) :=
      (summable_gaussKernel_centered (by positivity) hc12).mul_left _
    have hdom : ∀ k : Fin 3 → ℤ,
        ‖∑ i : Fin 3, iteratedDeriv 2 (gaussKernelSpaceLine τ i c k) (c i)‖ ≤
        10 / τ * gaussKernel (2 * τ) (c + fun j => (k j : ℝ)) := by
      intro k
      rw [hterm k, Real.norm_eq_abs]
      have := gauss_time_deriv_dom hτ0 (c + fun j => (k j : ℝ))
      simpa [Pi.add_apply] using this
    have hbound := tsum_of_norm_bounded hsum2.hasSum hdom
    unfold gaussKernelTimeDerivativeTsum
    rw [← Real.norm_eq_abs]
    refine hbound.trans ?_
    rw [tsum_mul_left]
    have hH : ∑' k : Fin 3 → ℤ, gaussKernel (2 * τ) (c + fun j => (k j : ℝ)) =
        heatKernel (2 * τ) (torusProj c) := by
      rw [heatKernel_comp_torusProj_eq_lift]
      rfl
    rw [hH]
    have hMb : heatKernel (2 * τ) (torusProj c) ≤ max M 0 :=
      (hM (2 * τ) (by linarith) _).trans (le_max_left _ _)
    have h4 : 10 / τ ≤ 20 := by
      rw [div_le_iff₀ hτ0]
      linarith
    exact mul_le_mul h4 hMb (heatKernel_nonneg (by linarith) _) (by norm_num)

end RegularityStructures

end
