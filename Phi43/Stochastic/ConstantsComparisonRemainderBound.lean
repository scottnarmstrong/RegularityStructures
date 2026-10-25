/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonKernelBridge
public import Phi43.Stochastic.ConstantsComparisonKernelLp
public import Phi43.Stochastic.ConstantsComparisonOrderOneFactor
public import RegularityStructures.Torus.KernelBoundsGaussian
public import RegularityStructures.Torus.KernelBoundsGlobal
public import RegularityStructures.Torus.KernelBoundsLargeTime
public import RegularityStructures.Analysis.Heat.Causal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import RegularityStructures.Analysis.Heat.Decomposition.Basic

/-!
# A local bound for the periodised smooth remainder

This file begins the analytic estimates for the comparison of the constants.  The singular part of
the periodised heat kernel is separated from the central lattice point.  The remaining Gaussian tail
is uniformly summable, while the cutoff in `heatRemainder` removes the central singularity. The
numerical constants are intentionally inessential.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

private def constantsComparisonTailMajorant (n : ℤ) : ℝ :=
  if n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) then
    2 + exp (-(n : ℝ) ^ 2 / 64)
  else exp (-(n : ℝ) ^ 2 / 64)

private theorem constantsComparisonTailMajorant_nonneg (n : ℤ) :
    0 ≤ constantsComparisonTailMajorant n := by
  unfold constantsComparisonTailMajorant
  split_ifs <;> positivity

private theorem summable_constantsComparisonTailMajorant :
    Summable constantsComparisonTailMajorant := by
  have hfinite : Summable (fun n : ℤ =>
      if n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) then (2 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := ({-3, -2, -1, 0, 1, 2} : Finset ℤ))
    intro n hn
    simp [hn]
  have hgauss : Summable (fun n : ℤ => exp (-(n : ℝ) ^ 2 / 64)) := by
    convert (summable_exp_neg_mul_sq_int (a := (1 / 64 : ℝ))
      (b := 0) (by norm_num) (by simp : (0 : ℝ) ∈ Ico 0 1)) using 1
    funext n
    congr 1
    ring
  convert hfinite.add hgauss using 1
  funext n
  unfold constantsComparisonTailMajorant
  split_ifs <;> ring

private theorem constantsComparisonTailMajorant_exp_shift_le
    {t y : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) (n : ℤ) :
    exp (-((y + (n : ℝ)) ^ 2) / (4 * t)) ≤
      exp (-y ^ 2 / (4 * t)) * constantsComparisonTailMajorant n := by
  have hbase := gaussian_shift_exp_le ht ht1 hy n
  unfold constantsComparisonTailMajorant
  by_cases hn : n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ)
  · simp [hn]
    unfold gaussianOneDimMajorant at hbase
    simp [hn] at hbase
    have hsmall : exp (-(4⁻¹ / 4 : ℝ) * (n : ℝ) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg (n : ℝ)]
    have hcoef : 1 + exp (-(4⁻¹ / 4 : ℝ) * (n : ℝ) ^ 2) ≤
        2 + exp (-(n : ℝ) ^ 2 / 64) := by
      nlinarith [hsmall, exp_nonneg (-(n : ℝ) ^ 2 / 64)]
    have hcoef' : 1 + exp (-(4⁻¹ / 4 * (n : ℝ) ^ 2)) ≤
        2 + exp (-(n : ℝ) ^ 2 / 64) := by
      simpa only [neg_mul] using hcoef
    exact hbase.trans (mul_le_mul_of_nonneg_left hcoef'
      (exp_nonneg (-y ^ 2 / (4 * t))))
  · simp [hn]
    unfold gaussianOneDimMajorant at hbase
    simp [hn] at hbase
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (n : ℝ)]))
      (exp_nonneg (-y ^ 2 / (4 * t))))

private theorem constantsComparisonTailMajorant_exp_shift_damped
    {t y : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) {n : ℤ}
    (hn : 1 / 48 < |y + (n : ℝ)|) :
    exp (-((y + (n : ℝ)) ^ 2) / (4 * t)) ≤
      exp (-(1 / 9216 : ℝ) / t) * constantsComparisonTailMajorant n := by
  by_cases hcentral : n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ)
  ·
    have hsq : (1 / 48 : ℝ) ^ 2 < (y + (n : ℝ)) ^ 2 := by
      have hsq' := (sq_lt_sq₀ (by positivity : 0 ≤ (1 / 48 : ℝ))
        (abs_nonneg (y + (n : ℝ)))).mpr hn
      simpa only [sq_abs] using hsq'
    have hexp : exp (-((y + (n : ℝ)) ^ 2) / (4 * t)) ≤
        exp (-(1 / 9216 : ℝ) / t) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [hsq]
    exact hexp.trans (by
      have htail : 1 ≤ constantsComparisonTailMajorant n := by
        unfold constantsComparisonTailMajorant
        rw [ite_eq_left hcentral]
        nlinarith [exp_nonneg (-(n : ℝ) ^ 2 / 64)]
      calc
        exp (-(1 / 9216 : ℝ) / t) =
            exp (-(1 / 9216 : ℝ) / t) * 1 := by ring
        _ ≤ exp (-(1 / 9216 : ℝ) / t) *
            constantsComparisonTailMajorant n :=
          mul_le_mul_of_nonneg_left htail (exp_nonneg _))
  ·
    have hsq := sq_centered_add_int_tail_ge hy hcentral
    have hnlarge : (9 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hn' : n ≤ -4 ∨ 3 ≤ n := by
        have hne : n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 := by
          simpa only [Finset.mem_insert, Finset.mem_singleton, not_or,
            not_false_eq_true] using hcentral
        omega
      rcases hn' with hn' | hn'
      · have hnr : (n : ℝ) ≤ -4 := by exact_mod_cast hn'
        nlinarith
      · have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn'
        nlinarith
    have hmain : (1 / 9216 : ℝ) / t + (n : ℝ) ^ 2 / 64 ≤
        (n : ℝ) ^ 2 / (8 * t) := by
      have ht0 : 0 < t := ht
      have ht1' : 0 < 1 / t := by positivity
      have hnt : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      have hscale : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).2 ht1
      field_simp
      nlinarith
    have hexp : exp (-((y + (n : ℝ)) ^ 2) / (4 * t)) ≤
        exp (-(1 / 9216 : ℝ) / t - (n : ℝ) ^ 2 / 64) := by
      apply Real.exp_le_exp.mpr
      have hy2 : 0 ≤ y ^ 2 := sq_nonneg _
      have hsq' : y ^ 2 + (n : ℝ) ^ 2 / 2 ≤ (y + (n : ℝ)) ^ 2 := hsq
      have hstep : -(y + (n : ℝ)) ^ 2 / (4 * t) ≤
          -y ^ 2 / (4 * t) - (n : ℝ) ^ 2 / (8 * t) := by
        rw [show -y ^ 2 / (4 * t) - (n : ℝ) ^ 2 / (8 * t) =
          (-y ^ 2 - (n : ℝ) ^ 2 / 2) / (4 * t) by ring]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      have hyterm : 0 ≤ y ^ 2 / (4 * t) := by positivity
      have hneg : -(n : ℝ) ^ 2 / (8 * t) ≤
          -(1 / 9216 : ℝ) / t - (n : ℝ) ^ 2 / 64 := by
        calc
          -(n : ℝ) ^ 2 / (8 * t) ≤
              -((1 / 9216 : ℝ) / t + (n : ℝ) ^ 2 / 64) := by
                have hneg' := neg_le_neg hmain
                convert hneg' using 1; ring
          _ = -(1 / 9216 : ℝ) / t - (n : ℝ) ^ 2 / 64 := by ring
      calc
        _ ≤ -y ^ 2 / (4 * t) - (n : ℝ) ^ 2 / (8 * t) := hstep
        _ ≤ -(n : ℝ) ^ 2 / (8 * t) := by
          have hnonpos : -y ^ 2 / (4 * t) ≤ 0 := by
            rw [show -y ^ 2 / (4 * t) = -(y ^ 2 / (4 * t)) by ring]
            exact neg_nonpos.mpr hyterm
          calc
            -y ^ 2 / (4 * t) - (n : ℝ) ^ 2 / (8 * t) =
                -(y ^ 2 / (4 * t)) - (n : ℝ) ^ 2 / (8 * t) := by ring
            _ ≤ 0 - (n : ℝ) ^ 2 / (8 * t) :=
              by
                have hsub := sub_le_sub_right hnonpos
                  ((n : ℝ) ^ 2 / (8 * t))
                convert hsub using 1; ring
            _ = -(n : ℝ) ^ 2 / (8 * t) := by ring
        _ ≤ _ := hneg
    calc
      _ ≤ exp (-(1 / 9216 : ℝ) / t - (n : ℝ) ^ 2 / 64) := hexp
      _ = exp (-(1 / 9216 : ℝ) / t) * exp (-(n : ℝ) ^ 2 / 64) := by
        rw [← exp_add]
        congr 1
        ring
      _ = exp (-(1 / 9216 : ℝ) / t) *
          constantsComparisonTailMajorant n := by
        have htail : constantsComparisonTailMajorant n =
            exp (-(n : ℝ) ^ 2 / 64) := by
          simp [constantsComparisonTailMajorant, hcentral]
        rw [htail]

private theorem constantsComparison_smooth_remainder_large_coordinate
    {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1 / 256)
    {y : Fin 3 → ℝ}
    (k : Fin 3 → ℤ)
    (hcut : 1 / 8 < smoothParabolicNorm
      (t, y + fun i => (k i : ℝ))) :
    ∃ i, 1 / 48 < |y i + (k i : ℝ)| := by
  by_contra h
  push Not at h
  have hroot : √t ≤ 1 / 16 := by
    have hsq : (√t) ^ 2 = t := Real.sq_sqrt ht.le
    have hnonneg : 0 ≤ √t := Real.sqrt_nonneg t
    nlinarith
  have hsum : ∑ i : Fin 3, |y i + (k i : ℝ)| ≤ 1 / 16 := by
    calc
      ∑ i : Fin 3, |y i + (k i : ℝ)| ≤
          ∑ i : Fin 3, (1 / 48 : ℝ) :=
        Finset.sum_le_sum fun i _ => h i
      _ = 1 / 16 := by norm_num [Finset.sum_const, Fintype.card_fin]
  have hpar : parabolicNorm (t, y + fun i => (k i : ℝ)) ≤ 1 / 8 := by
    unfold parabolicNorm
    calc
      √|t| + ∑ i : Fin 3, |(y + fun i => (k i : ℝ)) i| ≤
          1 / 16 + 1 / 16 := by
        rw [abs_of_pos ht]
        exact add_le_add hroot hsum
      _ = 1 / 8 := by norm_num
  have hpar' : smoothParabolicNorm (t, y + fun i => (k i : ℝ)) ≤ 1 / 8 :=
    le_trans (smoothParabolicNorm_le_parabolicNorm _) hpar
  exact (not_lt_of_ge hpar') hcut

private theorem constantsComparison_heatRemainder_term_abs_le_gauss
    {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    |heatRemainder (t, y + fun i => (k i : ℝ))| ≤
      gaussKernel t (y + fun i => (k i : ℝ)) := by
  rw [heatRemainder, abs_mul, heatKernelR4_of_pos ht,
    abs_of_nonneg (gaussKernel_nonneg ht _)]
  have hfactor : |1 - dyadicCutoff
      (2 ^ 3 * smoothParabolicNorm (t, y + fun i => (k i : ℝ)))| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [dyadicCutoff_nonneg
      (2 ^ 3 * smoothParabolicNorm (t, y + fun i => (k i : ℝ))),
      dyadicCutoff_le_one
      (2 ^ 3 * smoothParabolicNorm (t, y + fun i => (k i : ℝ)))]
  exact (mul_le_mul_of_nonneg_left hfactor (gaussKernel_nonneg ht _)).trans_eq
    (mul_one _)

private theorem constantsComparison_gaussKernel_damped
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {y : Fin 3 → ℝ} (hy : ∀ i, y i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (k : Fin 3 → ℤ) (hcoord : ∃ i, 1 / 48 < |y i + (k i : ℝ)|) :
    gaussKernel t (y + fun i => (k i : ℝ)) ≤
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        exp (-(1 / 9216 : ℝ) / t) *
          ∏ i, constantsComparisonTailMajorant (k i) := by
  obtain ⟨i0, hi0⟩ := hcoord
  have hpoint : ∀ i : Fin 3,
      exp (-((y i + (k i : ℝ)) ^ 2) / (4 * t)) ≤
        if i = i0 then
          exp (-(1 / 9216 : ℝ) / t) *
            constantsComparisonTailMajorant (k i)
        else constantsComparisonTailMajorant (k i) := by
    intro i
    by_cases hii : i = i0
    · subst i
      simpa using constantsComparisonTailMajorant_exp_shift_damped ht ht1
        (hy i0) hi0
    · rw [ite_eq_right hii]
      have hshift := constantsComparisonTailMajorant_exp_shift_le ht ht1 (hy i) (k i)
      exact hshift.trans (by
        have hnonneg : 0 ≤ exp (-y i ^ 2 / (4 * t)) := exp_nonneg _
        have hone : exp (-y i ^ 2 / (4 * t)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have hquot : 0 ≤ y i ^ 2 / (4 * t) := by positivity
          rw [show -y i ^ 2 / (4 * t) = -(y i ^ 2 / (4 * t)) by ring]
          exact neg_nonpos.mpr hquot
        exact mul_le_of_le_one_left
          (constantsComparisonTailMajorant_nonneg (k i)) hone)
  have hexpform : ∀ i : Fin 3,
      exp (-(4 * t)⁻¹ * (y i + (k i : ℝ)) ^ 2) =
        exp (-((y i + (k i : ℝ)) ^ 2) / (4 * t)) := by
    intro i
    congr 1
    ring
  rw [gaussKernel_eq_prod]
  simp_rw [Pi.add_apply, hexpform]
  have hprod :
      (∏ i, exp (-((y i + (k i : ℝ)) ^ 2) / (4 * t))) ≤
        ∏ i, if i = i0 then
          exp (-(1 / 9216 : ℝ) / t) *
            constantsComparisonTailMajorant (k i)
        else constantsComparisonTailMajorant (k i) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact exp_nonneg _
    · intro i hi
      exact hpoint i
  have hprod_eq :
      (∏ i, if i = i0 then
        exp (-(1 / 9216 : ℝ) / t) *
          constantsComparisonTailMajorant (k i)
      else constantsComparisonTailMajorant (k i)) =
        exp (-(1 / 9216 : ℝ) / t) *
          ∏ i, constantsComparisonTailMajorant (k i) := by
    fin_cases i0 <;> simp [Fin.prod_univ_three] <;> ring
  calc
    (4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ i, exp (-((y i + (k i : ℝ)) ^ 2) / (4 * t)) ≤
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ i, if i = i0 then
            exp (-(1 / 9216 : ℝ) / t) *
              constantsComparisonTailMajorant (k i)
          else constantsComparisonTailMajorant (k i) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (4 * π * t) ^ (-(3 : ℝ) / 2) *
          exp (-(1 / 9216 : ℝ) / t) *
            ∏ i, constantsComparisonTailMajorant (k i) := by
      rw [hprod_eq]
      ring

private theorem constantsComparison_heatRemainder_term_damped
    {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1 / 256)
    {y : Fin 3 → ℝ} (hy : ∀ i, y i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (k : Fin 3 → ℤ) :
    |heatRemainder (t, y + fun i => (k i : ℝ))| ≤
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        exp (-(1 / 9216 : ℝ) / t) *
          ∏ i, constantsComparisonTailMajorant (k i) := by
  by_cases hzero : heatRemainder (t, y + fun i => (k i : ℝ)) = 0
  · rw [hzero]
    have hpref : 0 ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) := by positivity
    have hprod : 0 ≤ ∏ i, constantsComparisonTailMajorant (k i) :=
      Finset.prod_nonneg fun i _ => constantsComparisonTailMajorant_nonneg (k i)
    simpa only [abs_zero] using
      (mul_nonneg (mul_nonneg hpref
        (exp_nonneg (-(1 / 9216 : ℝ) / t))) hprod)
  · have hcut : 1 / 8 < smoothParabolicNorm
        (t, y + fun i => (k i : ℝ)) := by
      by_contra hsmall
      have hsmall' : smoothParabolicNorm
          (t, y + fun i => (k i : ℝ)) ≤ 1 / 8 := le_of_not_gt hsmall
      have harg : (2 : ℝ) ^ 3 * smoothParabolicNorm
          (t, y + fun i => (k i : ℝ)) ≤ 1 := by
        nlinarith [smoothParabolicNorm_nonneg
          (t, y + fun i => (k i : ℝ))]
      rw [heatRemainder, dyadicCutoff_eq_one harg, sub_self, mul_zero] at hzero
      exact hzero rfl
    obtain ⟨i, hi⟩ := constantsComparison_smooth_remainder_large_coordinate
      ht htsmall k hcut
    exact (constantsComparison_heatRemainder_term_abs_le_gauss ht y k).trans
      (constantsComparison_gaussKernel_damped ht (by linarith) hy k ⟨i, hi⟩)

private theorem constantsComparison_damped_prefactor_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc (0 : ℝ) (1 / 256),
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        exp (-(1 / 9216 : ℝ) / t) ≤ B := by
  let B : ℝ := 512 * (48 : ℝ) ^ 3 * (4 * π) ^ (-(3 : ℝ) / 2)
  refine ⟨B, by positivity, ?_⟩
  intro t ht
  have htpos : 0 < t := ht.1
  have hsqrtpos : 0 < √t := Real.sqrt_pos.2 htpos
  let u : ℝ := (48 * √t)⁻¹
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hpoly := exp_neg_sq_div_four_mul_one_add_cube_le hu
  have huone : u ^ 3 ≤ (1 + u) ^ 3 := by
    exact pow_le_pow_left₀ hu (by linarith) 3
  have hpoly' : exp (-u ^ 2 / 4) * u ^ 3 ≤ 512 := by
    exact (mul_le_mul_of_nonneg_left huone (exp_nonneg _)).trans hpoly
  have hsq : (√t) ^ 2 = t := Real.sq_sqrt htpos.le
  have hexp : exp (-(1 / 9216 : ℝ) / t) = exp (-u ^ 2 / 4) := by
    congr 1
    dsimp [u]
    field_simp
    nlinarith [hsq]
  have htrpow : t ^ (-(3 : ℝ) / 2) = (√t)⁻¹ ^ (3 : ℕ) := by
    rw [show (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) by ring,
      Real.rpow_neg htpos.le, inv_pow]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
    ring_nf
  have hrel : (4 * π * t) ^ (-(3 : ℝ) / 2) *
        exp (-(1 / 9216 : ℝ) / t) =
      (4 * π) ^ (-(3 : ℝ) / 2) * (48 : ℝ) ^ 3 *
        (exp (-u ^ 2 / 4) * u ^ 3) := by
    rw [show 4 * π * t = (4 * π) * t by ring,
      Real.mul_rpow (by positivity) htpos.le, hexp]
    dsimp [u]
    rw [htrpow]
    field_simp
  rw [hrel]
  dsimp [B]
  calc
    (4 * π) ^ (-(3 : ℝ) / 2) * (48 : ℝ) ^ 3 *
        (exp (-u ^ 2 / 4) * u ^ 3) ≤
      (4 * π) ^ (-(3 : ℝ) / 2) * (48 : ℝ) ^ 3 * 512 :=
        mul_le_mul_of_nonneg_left hpoly' (by positivity)
    _ = 512 * (48 : ℝ) ^ 3 * (4 * π) ^ (-(3 : ℝ) / 2) := by ring

private theorem constantsComparison_tail_sum_bound :
    ∃ A : ℝ, 0 ≤ A ∧
      ∑' k : Fin 3 → ℤ, ∏ i, constantsComparisonTailMajorant (k i) ≤ A := by
  have hs := summable_constantsComparisonTailMajorant
  have hcube := tsum_fin3_prod_eq_cube hs constantsComparisonTailMajorant_nonneg
  refine ⟨(∑' n : ℤ, constantsComparisonTailMajorant n) ^ 3, ?_, ?_⟩
  · exact pow_nonneg (tsum_nonneg (fun n => constantsComparisonTailMajorant_nonneg n)) 3
  · rw [hcube]

private theorem constantsComparison_heatRemainder_centered_sum_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc (0 : ℝ) (1 / 256),
      ∀ y : Fin 3 → ℝ, (∀ i, y i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) →
        ∑' k : Fin 3 → ℤ,
          |heatRemainder (t, y + fun i => (k i : ℝ))| ≤ B := by
  obtain ⟨A, hA, hAt⟩ := constantsComparison_tail_sum_bound
  obtain ⟨P, hP, hPt⟩ := constantsComparison_damped_prefactor_bound
  let B : ℝ := P * A
  refine ⟨B, mul_nonneg hP hA, ?_⟩
  intro t ht y hy
  have htpos : 0 < t := ht.1
  let pref : ℝ := (4 * π * t) ^ (-(3 : ℝ) / 2) *
    exp (-(1 / 9216 : ℝ) / t)
  have hpref : 0 ≤ pref := by
    dsimp [pref]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (exp_nonneg _)
  have hprod : Summable (fun k : Fin 3 → ℤ =>
      ∏ i, constantsComparisonTailMajorant (k i)) :=
    summable_pi_fin3_prod summable_constantsComparisonTailMajorant
      constantsComparisonTailMajorant_nonneg
  have hright : Summable (fun k : Fin 3 → ℤ =>
      pref * ∏ i, constantsComparisonTailMajorant (k i)) := hprod.mul_left pref
  have hterm : ∀ k : Fin 3 → ℤ,
      |heatRemainder (t, y + fun i => (k i : ℝ))| ≤
        pref * ∏ i, constantsComparisonTailMajorant (k i) := by
    intro k
    simpa [pref] using constantsComparison_heatRemainder_term_damped
      ht.1 ht.2 hy k
  have hleft : Summable (fun k : Fin 3 → ℤ =>
      |heatRemainder (t, y + fun i => (k i : ℝ))|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hright
  have hsum := hleft.tsum_le_tsum hterm hright
  have hscalar : pref ≤ P := by
    dsimp [pref]
    exact hPt t ht
  calc
    ∑' k : Fin 3 → ℤ,
        |heatRemainder (t, y + fun i => (k i : ℝ))| ≤
      ∑' k : Fin 3 → ℤ,
        pref * ∏ i, constantsComparisonTailMajorant (k i) := hsum
    _ = pref * (∑' k : Fin 3 → ℤ,
        ∏ i, constantsComparisonTailMajorant (k i)) := by
      rw [tsum_mul_left]
    _ ≤ pref * A := mul_le_mul_of_nonneg_left hAt hpref
    _ ≤ P * A := mul_le_mul_of_nonneg_right hscalar hA
    _ = B := rfl

private theorem constantsComparison_heatRemainder_periodisation_small_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc (0 : ℝ) (1 / 256), ∀ x : Torus3,
      ∑' k : Fin 3 → ℤ,
        |heatRemainder (t, torusRep x + fun i => (k i : ℝ))| ≤ B := by
  obtain ⟨B, hB, hBt⟩ := constantsComparison_heatRemainder_centered_sum_bound
  refine ⟨B, hB, ?_⟩
  intro t ht x
  obtain ⟨m, hm⟩ := torusRep_eq_centered_add_int x
  have hy : ∀ i, torusCenteredRep x i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    fun i => torusCenteredRep_mem_Icc x i
  calc
    ∑' k : Fin 3 → ℤ,
        |heatRemainder (t, torusRep x + fun i => (k i : ℝ))| =
      ∑' k : Fin 3 → ℤ,
        |heatRemainder (t, torusCenteredRep x +
          fun i => ((m i + k i : ℤ) : ℝ))| := by
      apply tsum_congr
      intro k
      congr 2
      rw [hm]
      congr 1
      funext i
      simp only [Pi.add_apply, Int.cast_add]
      ring
    _ = ∑' k : Fin 3 → ℤ,
        |heatRemainder (t, torusCenteredRep x +
          fun i => (k i : ℝ))| := by
      simpa [Equiv.coe_addRight, Pi.add_apply, add_comm] using
        (Equiv.addRight m).tsum_eq (fun k : Fin 3 → ℤ =>
          |heatRemainder (t, torusCenteredRep x +
            fun i => (k i : ℝ))|)
    _ ≤ B := hBt t ht (torusCenteredRep x) hy

private theorem constantsComparison_heatRemainder_periodisation_medium_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc (1 / 256 : ℝ) 1, ∀ x : Torus3,
      ∑' k : Fin 3 → ℤ,
        |heatRemainder (t, torusRep x + fun i => (k i : ℝ))| ≤ B := by
  obtain ⟨C, hC⟩ := heatKernel_le_time_singular
  let A : ℝ := max C 0
  let B : ℝ := 4096 * A
  have hA : 0 ≤ A := le_max_right C 0
  refine ⟨B, mul_nonneg (by norm_num) hA, ?_⟩
  intro t ht x
  have htpos : 0 < t := lt_trans (by norm_num) ht.1
  have hs := summable_gaussKernel_shift htpos (torusRep x)
    (fun i => torusRep_mem_Ico x i)
  have hterm : ∀ k : Fin 3 → ℤ,
      |heatRemainder (t, torusRep x + fun i => (k i : ℝ))| ≤
        gaussKernel t (torusRep x + fun i => (k i : ℝ)) := by
    intro k
    exact constantsComparison_heatRemainder_term_abs_le_gauss htpos
      (torusRep x) k
  have hsum : (∑' k : Fin 3 → ℤ,
      |heatRemainder (t, torusRep x + fun i => (k i : ℝ))|) ≤
      heatKernel t x := by
    have hleft : Summable (fun k : Fin 3 → ℤ =>
        |heatRemainder (t, torusRep x + fun i => (k i : ℝ))|) :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hs
    have hle := hleft.tsum_le_tsum hterm hs
    simpa [heatKernel] using hle
  have hheat := hC t (by exact ⟨htpos, ht.2⟩) x
  have hpow : t ^ (-(3 : ℝ) / 2) ≤ (1 / 256 : ℝ) ^ (-(3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) ht.1.le (by norm_num)
  have hpow' : t ^ (-(3 : ℝ) / 2) ≤ 4096 := by
    calc
      t ^ (-(3 : ℝ) / 2) ≤ (1 / 256 : ℝ) ^ (-(3 : ℝ) / 2) := hpow
      _ ≤ 4096 := by norm_num [Real.rpow_neg]
  calc
    ∑' k : Fin 3 → ℤ,
        |heatRemainder (t, torusRep x + fun i => (k i : ℝ))| ≤
      heatKernel t x := hsum
    _ ≤ C * t ^ (-(3 : ℝ) / 2) := hheat
    _ ≤ A * t ^ (-(3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0)
        (Real.rpow_nonneg htpos.le _)
    _ ≤ A * 4096 := mul_le_mul_of_nonneg_left hpow' hA
    _ = B := by dsimp [B]; ring

private noncomputable def constantsComparison_annBumpIntegerBox :
    Finset (Fin 3 → ℤ) := by
  classical
  exact (Finset.univ.pi (fun _ : Fin 3 => Finset.Icc (-3 : ℤ) 3)).image
    (fun q i => q i (Finset.mem_univ i))

private theorem constantsComparison_annBump_contributing_mem_box
    {N : ℕ} {z : SpaceTime} {k : Fin 3 → ℤ}
    (hk : annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ)) ≠ 0) :
    k ∈ constantsComparison_annBumpIntegerBox := by
  obtain ⟨m, hm⟩ := torusRep_eq_centered_add_int z.2
  have hs : parabolicNorm
      (z.1, torusRep z.2 + fun i => (k i : ℝ)) ≤ 1 := by
    by_contra h
    exact hk (annBumpC_eq_zero (lt_of_not_ge h))
  have hcoord : ∀ i : Fin 3,
      |torusRep z.2 i + (k i : ℝ)| ≤ 1 := by
    intro i
    have hsum : |torusRep z.2 i + (k i : ℝ)| ≤
        ∑ j, |torusRep z.2 j + (k j : ℝ)| :=
      Finset.single_le_sum (s := Finset.univ) (f := fun j =>
        |torusRep z.2 j + (k j : ℝ)|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    have hpar : √|z.1| + ∑ j, |torusRep z.2 j + (k j : ℝ)| ≤ 1 := by
      simpa [parabolicNorm] using hs
    by_contra hi
    have hi' : 1 < |torusRep z.2 i + (k i : ℝ)| := lt_of_not_ge hi
    linarith [Real.sqrt_nonneg |z.1|]
  classical
  apply Finset.mem_image.mpr
  refine ⟨(fun i _ => k i), ?_, ?_⟩
  · apply Finset.mem_pi.mpr
    intro i hi
    apply Finset.mem_Icc.mpr
    have hcenter := torusCenteredRep_mem_Icc z.2 i
    have hi' : torusRep z.2 i + (k i : ℝ) =
        torusCenteredRep z.2 i + ((m i + k i : ℤ) : ℝ) := by
      rw [hm]
      simp only [Pi.add_apply, Int.cast_add]
      ring
    have hcoord_i := hcoord i
    rw [hi'] at hcoord_i
    have hq : (-2 : ℝ) ≤ (m i + k i : ℤ) ∧
        ((m i + k i : ℤ) : ℝ) ≤ 2 := by
      have hcoord_le := abs_le.mp hcoord_i
      constructor <;> linarith [hcoord_le.1, hcoord_le.2, hcenter.1, hcenter.2]
    have hq' : (-2 : ℤ) ≤ m i + k i ∧ m i + k i ≤ (2 : ℤ) := by
      exact_mod_cast hq
    have hm_i : (0 : ℤ) ≤ m i ∧ m i ≤ 1 := by
      have hrep := torusRep_mem_Ico z.2 i
      have heq : (m i : ℝ) = torusRep z.2 i - torusCenteredRep z.2 i := by
        have hi'' := congrFun hm i
        simp only [Pi.add_apply] at hi''
        linarith
      have hlo : (-1 : ℝ) < (m i : ℝ) := by linarith [hrep.1, hcenter.2, heq]
      have hhi : (m i : ℝ) < 2 := by linarith [hrep.2, hcenter.1, heq]
      have hlo' : (-1 : ℤ) < m i := by exact_mod_cast hlo
      have hhi' : m i < (2 : ℤ) := by exact_mod_cast hhi
      constructor <;> omega
    have hki : (-3 : ℤ) ≤ k i ∧ k i ≤ (3 : ℤ) := by
      constructor <;> omega
    exact hki
  · funext i
    simp

private theorem constantsComparison_annBump_periodisation_bound (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : SpaceTime,
      ∑' k : Fin 3 → ℤ,
        |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤ B := by
  obtain ⟨BB, hBB⟩ := (contDiff_annBumpC N).continuous.abs.bounded_above_of_compact_support
    (hasCompactSupport_of_eq_zero_unit (fun _ hz => annBumpC_eq_zero hz)).norm
  let S := constantsComparison_annBumpIntegerBox
  let B : ℝ := S.card * max BB 0
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro z
  have hsum : (∑' k : Fin 3 → ℤ,
      |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) =
      ∑ k ∈ S, |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| := by
    rw [tsum_eq_sum]
    intro k hk
    by_contra hne
    apply hk
    exact constantsComparison_annBump_contributing_mem_box
      (by simpa only [abs_ne_zero] using hne)
  have hterm : ∀ k ∈ S,
      |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤ max BB 0 := by
    intro k hk
    simpa only [Real.norm_eq_abs, abs_abs] using
      (hBB (z.1, torusRep z.2 + fun i => (k i : ℝ))).trans
        (le_max_left BB 0)
  calc
    ∑' k : Fin 3 → ℤ,
        |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| =
      ∑ k ∈ S, |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| := hsum
    _ ≤ ∑ k ∈ S, max BB 0 := Finset.sum_le_sum fun k hk => hterm k hk
    _ = B := by
      dsimp [B]
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]

private theorem constantsComparison_heatRemainder_periodisation_summable
    {t : ℝ} (ht : 0 < t) (x : Torus3) :
    Summable (fun k : Fin 3 → ℤ =>
      |heatRemainder (t, torusRep x + fun i => (k i : ℝ))|) := by
  have hs := summable_gaussKernel_shift ht (torusRep x)
    (fun i => torusRep_mem_Ico x i)
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
  · intro k
    exact constantsComparison_heatRemainder_term_abs_le_gauss ht
      (torusRep x) k
  · exact hs

private theorem constantsComparison_annBump_periodisation_summable (N : ℕ)
    (z : SpaceTime) :
    Summable (fun k : Fin 3 → ℤ =>
      |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) := by
  apply summable_of_hasFiniteSupport
  refine constantsComparison_annBumpIntegerBox.finite_toSet.subset ?_
  intro k hk
  by_contra hne
  have hnonzero : annBumpC N
      (z.1, torusRep z.2 + fun i => (k i : ℝ)) ≠ 0 := by
    simpa only [Function.mem_support, abs_ne_zero] using hk
  exact hne (constantsComparison_annBump_contributing_mem_box hnonzero)

private theorem constantsComparison_annRemainder_periodisation_summable (N : ℕ)
    (z : SpaceTime) :
    Summable (fun k : Fin 3 → ℤ =>
      |annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) := by
  have hbumps := constantsComparison_annBump_periodisation_summable N z
  by_cases ht : z.1 ≤ 0
  · have hheat : ∀ k : Fin 3 → ℤ,
        |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))| = 0 := by
      intro k
      rw [heatRemainder, heatKernelR4_of_nonpos ht, zero_mul, abs_zero]
    have hhs : Summable (fun k : Fin 3 → ℤ =>
        |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))|) := by
      apply summable_zero.congr
      intro k
      exact (hheat k).symm
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) ?_ (hhs.add hbumps)
    intro k
    simpa only [annRemainderC] using abs_add_le
      (heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ)))
      (annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ)))
  · have hhs := constantsComparison_heatRemainder_periodisation_summable
      (lt_of_not_ge ht) z.2
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) ?_ (hhs.add hbumps)
    intro k
    simpa only [annRemainderC] using abs_add_le
      (heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ)))
      (annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ)))

private theorem constantsComparison_annRemainder_periodisation_bound (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : SpaceTime, -1 ≤ z.1 → z.1 ≤ 1 →
      ∑' k : Fin 3 → ℤ,
        |annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤ B := by
  obtain ⟨Bs, hBs, hBst⟩ :=
    constantsComparison_heatRemainder_periodisation_small_bound
  obtain ⟨Bm, hBm, hBmt⟩ :=
    constantsComparison_heatRemainder_periodisation_medium_bound
  obtain ⟨Bb, hBb, hBbt⟩ := constantsComparison_annBump_periodisation_bound N
  let B : ℝ := Bs + Bm + Bb
  refine ⟨B, by positivity, ?_⟩
  intro z hz0 hz1
  have hbump := hBbt z
  have hbumps := constantsComparison_annBump_periodisation_summable N z
  by_cases ht : z.1 ≤ 0
  · have hheat : ∀ k : Fin 3 → ℤ,
        |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))| = 0 := by
      intro k
      rw [heatRemainder, heatKernelR4_of_nonpos ht, zero_mul, abs_zero]
    have hhs : Summable (fun k : Fin 3 → ℤ =>
        |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))|) := by
      apply summable_zero.congr
      intro k
      exact (hheat k).symm
    have hsum : ∑' k : Fin 3 → ℤ,
        |annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤ Bb := by
      have hterm : ∀ k : Fin 3 → ℤ,
          |annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤
            |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))| +
              |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| := by
        intro k
        rw [annRemainderC]
        exact abs_add_le _ _
      have hdom : Summable (fun k : Fin 3 → ℤ =>
          |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))| +
            |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) := by
        exact hhs.add hbumps
      have hleft := Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
        hterm hdom
      calc
        _ ≤ ∑' k : Fin 3 → ℤ,
            (|heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))| +
              |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) :=
          hleft.tsum_le_tsum hterm hdom
        _ = (∑' k : Fin 3 → ℤ,
            |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))|) +
              (∑' k : Fin 3 → ℤ,
            |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) := by
          rw [hhs.tsum_add hbumps]
        _ ≤ Bb := by simpa [hheat, add_zero] using hbump
    exact hsum.trans (by dsimp [B]; linarith [hBs, hBm])
  · have htpos : 0 < z.1 := lt_of_not_ge ht
    by_cases hsmall : z.1 ≤ 1 / 256
    · have hheat := hBst z.1 ⟨htpos, hsmall⟩ z.2
      have hhs := constantsComparison_heatRemainder_periodisation_summable htpos z.2
      have hterm : ∀ k : Fin 3 → ℤ,
          |annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤
            |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))| +
              |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| := by
        intro k
        rw [annRemainderC]
        exact abs_add_le _ _
      have hdom : Summable (fun k : Fin 3 → ℤ =>
          |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))| +
            |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) := hhs.add hbumps
      have hleft := Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
        hterm hdom
      calc
        _ ≤ (∑' k : Fin 3 → ℤ,
            |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))|) +
              (∑' k : Fin 3 → ℤ,
            |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) := by
          rw [← hhs.tsum_add hbumps]
          exact hleft.tsum_le_tsum hterm hdom
        _ ≤ Bs + Bb := add_le_add hheat hbump
        _ ≤ B := by dsimp [B]; linarith [hBm]
    · have hmedium : (1 / 256 : ℝ) < z.1 := lt_of_not_ge hsmall
      have hheat := hBmt z.1 ⟨hmedium, hz1⟩ z.2
      have hhs := constantsComparison_heatRemainder_periodisation_summable htpos z.2
      have hterm : ∀ k : Fin 3 → ℤ,
          |annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤
            |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))| +
              |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| := by
        intro k
        rw [annRemainderC]
        exact abs_add_le _ _
      have hdom : Summable (fun k : Fin 3 → ℤ =>
          |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))| +
            |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) := hhs.add hbumps
      have hleft := Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
        hterm hdom
      calc
        _ ≤ (∑' k : Fin 3 → ℤ,
            |heatRemainder (z.1, torusRep z.2 + fun i => (k i : ℝ))|) +
              (∑' k : Fin 3 → ℤ,
            |annBumpC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) := by
          rw [← hhs.tsum_add hbumps]
          exact hleft.tsum_le_tsum hterm hdom
        _ ≤ Bm + Bb := add_le_add hheat hbump
        _ ≤ B := by dsimp [B]; linarith [hBs]

theorem constantsComparisonR_orderOne_ae (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ z : SpaceTime ∂volume,
      0 < torusParabolicSize z → torusParabolicSize z ≤ 1 →
        |constantsComparisonR N z| ≤ C * torusParabolicSize z ^ (-1 : ℝ) := by
  obtain ⟨Cfactor, hCfactor, hfactor⟩ :=
    constantsComparison_massive_factor_order_one
  obtain ⟨Bann, hBann, hAnn⟩ :=
    constantsComparison_annRemainder_periodisation_bound N
  have hbridge := constantsComparisonR_eq_periodised_orderOne_ae N
  let C : ℝ := Real.exp 1 * Cfactor + Bann
  refine ⟨C, by positivity, ?_⟩
  filter_upwards [hbridge] with z hzbridge
  intro hsizepos hsmall
  have htbound : -1 ≤ z.1 ∧ z.1 ≤ 1 := by
    have hroot : √|z.1| ≤ 1 := by
      have hs := torusParabolicSize_eq_time_spatial z
      nlinarith [hs, hsmall, torusSpatialNorm_nonneg z.2,
        Real.sqrt_nonneg |z.1|, Real.sqrt_nonneg (sqNorm3 (torusCenteredRep z.2))]
    have hsq := Real.sq_sqrt (abs_nonneg z.1)
    have habs : |z.1| ≤ 1 := by
      nlinarith [hsq, hroot, Real.sqrt_nonneg |z.1|]
    exact abs_le.mp habs
  have hAnn' := hAnn z htbound.1 htbound.2
  have hsumAnn := constantsComparison_annRemainder_periodisation_summable N z
  have hann : Summable (fun k : Fin 3 → ℤ =>
      annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hsumAnn
  by_cases ht : z.1 ≤ 0
  · have hheat : ∀ k : Fin 3 → ℤ,
          heatKernelR4 (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0 := by
        intro k
        exact heatKernelR4_of_nonpos ht
    have hfactorSum : ∑' k : Fin 3 → ℤ,
        ((Real.exp (-z.1) - 1) * heatKernelR4
          (z.1, torusRep z.2 + fun i => (k i : ℝ))) = 0 := by
      have hfun : (fun k : Fin 3 → ℤ =>
          (Real.exp (-z.1) - 1) * heatKernelR4
            (z.1, torusRep z.2 + fun i => (k i : ℝ))) = fun _ => 0 := by
        funext k
        rw [hheat k, mul_zero]
      rw [hfun]
      simp
    have hfactorSummable : Summable (fun k : Fin 3 → ℤ =>
        (Real.exp (-z.1) - 1) * heatKernelR4
          (z.1, torusRep z.2 + fun i => (k i : ℝ))) := by
      apply summable_zero.congr
      intro k
      simp [hheat k]
    have hsplit := hfactorSummable.tsum_add hann
    rw [hzbridge, hsplit, hfactorSum, zero_add]
    have hBweight : Bann ≤ Bann * torusParabolicSize z ^ (-1 : ℝ) := by
      have hpow : 1 ≤ torusParabolicSize z ^ (-1 : ℝ) := by
        rw [Real.rpow_neg hsizepos.le]
        simpa only [Real.rpow_one] using (one_le_inv₀ hsizepos).2 hsmall
      calc
        Bann = Bann * 1 := by rw [mul_one]
        _ ≤ Bann * torusParabolicSize z ^ (-1 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow hBann
    have hsumNorm : |∑' k : Fin 3 → ℤ,
        annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤ Bann := by
      have h := norm_tsum_le_tsum_norm hann.norm
      simpa only [Real.norm_eq_abs] using h.trans hAnn'
    calc
      |∑' k : Fin 3 → ℤ,
          annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤ Bann := hsumNorm
      _ ≤ Bann * torusParabolicSize z ^ (-1 : ℝ) := hBweight
      _ ≤ C * torusParabolicSize z ^ (-1 : ℝ) := by
        have hpow' : 0 ≤ torusParabolicSize z ^ (-1 : ℝ) :=
          Real.rpow_nonneg hsizepos.le _
        have hscalar : Bann ≤ Real.exp 1 * Cfactor + Bann := by
          have : 0 ≤ Real.exp 1 * Cfactor := by positivity
          linarith
        exact mul_le_mul_of_nonneg_right hscalar hpow'
  · have htpos : 0 < z.1 := lt_of_not_ge ht
    have hsumHeat : Summable (fun k : Fin 3 → ℤ =>
        heatKernelR4 (z.1, torusRep z.2 + fun i => (k i : ℝ))) := by
      have hs := summable_gaussKernel_shift htpos (torusRep z.2)
        (fun i => torusRep_mem_Ico z.2 i)
      apply hs.congr
      intro k
      rw [heatKernelR4_of_pos htpos]
    have hsumFactor : Summable (fun k : Fin 3 → ℤ =>
        (Real.exp (-z.1) - 1) * heatKernelR4
          (z.1, torusRep z.2 + fun i => (k i : ℝ))) :=
      hsumHeat.mul_left _
    have hsumAll := hsumFactor.add hann
    have hsumFactorEq : ∑' k : Fin 3 → ℤ,
        (Real.exp (-z.1) - 1) * heatKernelR4
          (z.1, torusRep z.2 + fun i => (k i : ℝ)) =
        (Real.exp (-z.1) - 1) * heatKernel z.1 z.2 := by
      rw [tsum_mul_left]
      congr 1
      rw [heatKernel]
      apply tsum_congr
      intro k
      rw [heatKernelR4_of_pos htpos]
    have hfactorAbs : |(Real.exp (-z.1) - 1) * heatKernel z.1 z.2| ≤
        Real.exp 1 * Cfactor * torusParabolicSize z ^ (-1 : ℝ) := by
      have hmass := hfactor z hsizepos
      have hmassEq : massiveHeatKernel z =
          Real.exp (-z.1) * heatKernel z.1 z.2 := by
        simp only [massiveHeatKernel, htpos, ite_true]
      have hheatEq : heatKernel z.1 z.2 = Real.exp z.1 * massiveHeatKernel z := by
        rw [hmassEq]
        rw [← mul_assoc, ← Real.exp_add]
        simp
      calc
        |(Real.exp (-z.1) - 1) * heatKernel z.1 z.2| =
            Real.exp z.1 * |(Real.exp (-z.1) - 1) * massiveHeatKernel z| := by
          rw [hheatEq]
          simp only [abs_mul, abs_of_pos (Real.exp_pos z.1),
            abs_of_nonneg (massiveHeatKernel_nonneg z)]
          ring
        Real.exp z.1 * |(Real.exp (-z.1) - 1) * massiveHeatKernel z| ≤
            Real.exp z.1 * (Cfactor * torusParabolicSize z ^ (-1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
        _ ≤ Real.exp 1 * (Cfactor * torusParabolicSize z ^ (-1 : ℝ)) := by
          gcongr
          exact htbound.2
        _ = Real.exp 1 * Cfactor * torusParabolicSize z ^ (-1 : ℝ) := by ring
    have hdom : Summable (fun k : Fin 3 → ℤ =>
        |(Real.exp (-z.1) - 1) * heatKernelR4
            (z.1, torusRep z.2 + fun i => (k i : ℝ))| +
          |annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) := by
      exact hsumFactor.norm.add hsumAnn
    have hpoint : ∀ k : Fin 3 → ℤ,
        |(Real.exp (-z.1) - 1) * heatKernelR4
            (z.1, torusRep z.2 + fun i => (k i : ℝ)) +
          annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤
          |(Real.exp (-z.1) - 1) * heatKernelR4
            (z.1, torusRep z.2 + fun i => (k i : ℝ))| +
          |annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))| := by
      intro k
      exact abs_add_le _ _
    have habsAll : Summable (fun k : Fin 3 → ℤ =>
        |(Real.exp (-z.1) - 1) * heatKernelR4
            (z.1, torusRep z.2 + fun i => (k i : ℝ)) +
          annRemainderC N (z.1, torusRep z.2 + fun i => (k i : ℝ))|) :=
      hsumAll.norm
    have hsumPoint := habsAll.tsum_le_tsum hpoint hdom
    have hnormBridge := (norm_tsum_le_tsum_norm hsumAll.norm).trans hsumPoint
    have hheatKernelSum : ∑' k : Fin 3 → ℤ,
        heatKernelR4 (z.1, torusRep z.2 + fun i => (k i : ℝ)) =
        heatKernel z.1 z.2 := by
      rw [heatKernel]
      apply tsum_congr
      intro k
      rw [heatKernelR4_of_pos htpos]
    have hfactorNorm : ∑' k : Fin 3 → ℤ,
        |(Real.exp (-z.1) - 1) * heatKernelR4
            (z.1, torusRep z.2 + fun i => (k i : ℝ))| =
        |(Real.exp (-z.1) - 1) * heatKernel z.1 z.2| := by
      calc
        _ = ∑' k : Fin 3 → ℤ,
            |Real.exp (-z.1) - 1| * heatKernelR4
              (z.1, torusRep z.2 + fun i => (k i : ℝ)) := by
          apply tsum_congr
          intro k
          rw [abs_mul, abs_of_nonneg (heatKernelR4_nonneg _)]
        _ = |Real.exp (-z.1) - 1| *
            (∑' k : Fin 3 → ℤ,
              heatKernelR4 (z.1, torusRep z.2 + fun i => (k i : ℝ))) := by
          rw [tsum_mul_left]
        _ = |(Real.exp (-z.1) - 1) * heatKernel z.1 z.2| := by
          rw [hheatKernelSum, abs_mul,
            abs_of_nonneg (heatKernel_nonneg htpos z.2)]
    calc
      |constantsComparisonR N z| ≤
          |(Real.exp (-z.1) - 1) * heatKernel z.1 z.2| + Bann := by
        rw [hzbridge]
        exact hnormBridge.trans (by
          calc
            (∑' i : Fin 3 → ℤ, (|(Real.exp (-z.1) - 1) * heatKernelR4
                    (z.1, torusRep z.2 + fun j => (i j : ℝ))| +
                  |annRemainderC N
                    (z.1, torusRep z.2 + fun j => (i j : ℝ))|)) =
                |(Real.exp (-z.1) - 1) * heatKernel z.1 z.2| +
                  (∑' i : Fin 3 → ℤ,
                    |annRemainderC N
                      (z.1, torusRep z.2 + fun j => (i j : ℝ))|) := by
              calc
                _ = (∑' i : Fin 3 → ℤ,
                    |(Real.exp (-z.1) - 1) * heatKernelR4
                        (z.1, torusRep z.2 + fun j => (i j : ℝ))|) +
                    (∑' i : Fin 3 → ℤ,
                      |annRemainderC N
                        (z.1, torusRep z.2 + fun j => (i j : ℝ))|) := by
                  simpa only [Real.norm_eq_abs] using
                    hsumFactor.norm.tsum_add hsumAnn
                _ = _ := by rw [hfactorNorm]
            _ ≤ |(Real.exp (-z.1) - 1) * heatKernel z.1 z.2| + Bann :=
              add_le_add (le_refl _) hAnn')
      _ ≤ Real.exp 1 * Cfactor * torusParabolicSize z ^ (-1 : ℝ) + Bann :=
        add_le_add hfactorAbs (le_refl _)
      _ ≤ C * torusParabolicSize z ^ (-1 : ℝ) := by
        have hpow : 1 ≤ torusParabolicSize z ^ (-1 : ℝ) := by
          rw [Real.rpow_neg hsizepos.le]
          simpa only [Real.rpow_one] using (one_le_inv₀ hsizepos).2 hsmall
        have hpow' : 0 ≤ torusParabolicSize z ^ (-1 : ℝ) :=
          Real.rpow_nonneg hsizepos.le _
        dsimp [C]
        have hBweight : Bann ≤ Bann * torusParabolicSize z ^ (-1 : ℝ) := by
          calc
            Bann = Bann * 1 := by rw [mul_one]
            _ ≤ Bann * torusParabolicSize z ^ (-1 : ℝ) :=
              mul_le_mul_of_nonneg_left hpow hBann
        calc
          Real.exp 1 * Cfactor * torusParabolicSize z ^ (-1 : ℝ) + Bann ≤
              Real.exp 1 * Cfactor * torusParabolicSize z ^ (-1 : ℝ) +
                Bann * torusParabolicSize z ^ (-1 : ℝ) :=
            add_le_add (le_refl _) hBweight
          _ = (Real.exp 1 * Cfactor + Bann) *
              torusParabolicSize z ^ (-1 : ℝ) := by ring

end RegularityStructures.Phi43

end
